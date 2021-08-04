//
//  PrettyPrinter.swift
//  
//
//  Created by Steven Obua on 04/08/2021.
//

import Foundation

public final class PrettyPrinter {
    
    public typealias Priority = ConcreteSyntax.Priority
        
    public enum Fragment {
        case Var(Var)
        case Const(Const)
        case Space
        case Text(String)
        case Keyword(String)
        case Tree(Tree, brackets : Bool)
    }
    
    public struct Tree {
        public var fragments : [Fragment]
        public let priority : Priority
        public init(fragments : [Fragment] = [], priority : Priority) {
            self.fragments = fragments
            self.priority = priority
        }
        public mutating func append(_ fragment : Fragment) {
            fragments.append(fragment)
        }
        public mutating func append(_ text : String) {
            fragments.append(.Text(text))
        }
        public mutating func space() {
            fragments.append(.Space)
        }
        public mutating func append(_ tree : Tree, brackets : Bool) {
            fragments.append(.Tree(tree, brackets: brackets))
        }
        public var isAtomic : Bool {
            switch priority {
            case .Atomic: return true
            default: return false
            }
        }
    }
    
    private struct Match {
        let syntaxPattern : SyntaxPattern
        let concreteSyntax : ConcreteSyntax
        let binders : [Var : Var]
        let terms : [Var : Term]
    }
    
    private let patterns : [(SyntaxPattern, ConcreteSyntax)]
    
    public init(patterns : [(SyntaxPattern, ConcreteSyntax)] = []) {
        self.patterns = patterns
    }
    
    public init(patterns : [(SyntaxPattern, [ConcreteSyntax])]) {
        var ps : [(SyntaxPattern, ConcreteSyntax)] = []
        for (pattern, css) in patterns {
            if !css.isEmpty {
                ps.append((pattern, css.first!))
            }
        }
        self.patterns = ps
    }

    private func printRaw(const : Const, binders : [Var], params : [Term]) -> Tree {
        var tree = Tree(priority: .Atomic)
        tree.append("(")
        tree.append(.Const(const))
        for v in binders {
            tree.space()
            tree.append(.Var(v))
        }
        tree.append(".")
        for p in params {
            tree.space()
            let t = printAsTree(p)
            tree.append(t, brackets: !t.isAtomic)
        }
        tree.append(")")
        return tree
    }
        
    private func matchPattern(_ pattern : SyntaxPattern, _ term : Term) -> (binders : [Var : Var], terms : [Var : Term])? {
        var bound : [Var : Var] = [:]
        var terms : [Var : Term] = [:]
        func match(_ pattern : SyntaxPattern, _ term : Term) -> Bool {
            switch pattern {
            case let .variable(v):
                terms[v] = term
                return true
            case let .constant(const, binders: binders, params: params):
                switch term {
                case .variable: return false
                case let .constant(const2, binders: binders2, params: params2):
                    guard const == const2 else { return false }
                    guard binders.count == binders2.count else { return false }
                    guard params.count == params2.count else { return false }
                    for i in 0 ..< binders.count {
                        bound[binders[i]] = binders2[i]
                    }
                    for i in 0 ..< params.count {
                        guard match(params[i], params2[i]) else { return false }
                    }
                    return true
                }
            }
        }
        if match(pattern, term) {
            return (bound, terms)
        } else {
            return nil
        }
    }
    
    private func findMatch(_ term : Term) -> Match? {
        for (pattern, concreteSyntax) in patterns {
            if let (binders, terms) = matchPattern(pattern, term) {
                return Match(syntaxPattern: pattern, concreteSyntax: concreteSyntax, binders: binders, terms: terms)
            }
        }
        return nil
    }
        
    private func needsBrackets(_ expr : Priority, _ subExpr : Priority, raised : Bool) -> Bool {
        switch (expr, subExpr) {
        case (_, .Atomic): return false
        case (.Atomic, _): return true
        case (.None, _): return true
        case (_, .None): return true
        case let (.Level(u), .Level(v)):
            let noBracketsNeeded = v > u || (!raised && v == u)
            return !noBracketsNeeded
        }
    }
        
    private func printMatch(_ match : Match) -> Tree {
        let priority = match.concreteSyntax.priority
        var tree = Tree(priority: priority)
        for f in match.concreteSyntax.fragments {
            switch f {
            case let .Keyword(keyword): tree.append(.Keyword(keyword))
            case .Space: tree.space()
            case let .Text(text): tree.append(text)
            case let .Var(v, raised: raised):
                if let w = match.binders[v] {
                    tree.append(.Var(w))
                } else if let term = match.terms[v] {
                    let subtree = printAsTree(term)
                    let brackets = needsBrackets(priority, subtree.priority, raised: raised)
                    tree.append(subtree, brackets: brackets)
                } else {
                    fatalError()
                }
            }
        }
        return tree
    }
    
    private func printAsTree(_ term : Term) -> Tree {
        switch term {
        case let .variable(v, params: params):
            var tree = Tree(priority: .Atomic)
            tree.append(.Var(v))
            if !params.isEmpty {
                tree.append("[")
                tree.append(printAsTree(params.first!), brackets: false)
                for p in params.dropFirst() {
                    tree.append(",")
                    tree.space()
                    tree.append(printAsTree(p), brackets: false)
                }
                tree.append("]")
            }
            return tree
        case let .constant(const, binders: binders, params: params):
            if let match = findMatch(term) {
                return printMatch(match)
            } else {
                return printRaw(const: const, binders: binders, params: params)
            }
        }
    }
        
    public func printTerm(_ term : Term) -> String {
        let tree = printAsTree(term)
        return PrettyPrinter.printTree(tree)
    }

    public static func printTree(_ tree : Tree) -> String {
        var s : String = ""
        for f in tree.fragments {
            switch f {
            case let .Const(c): s.append(c.description)
            case let .Var(v): s.append(v.description)
            case let .Keyword(keyword): s.append(keyword)
            case .Space: s.append(" ")
            case let .Text(text): s.append(text)
            case let .Tree(tree, brackets: brackets):
                if brackets {
                    s.append("(")
                }
                s.append(printTree(tree))
                if brackets {
                    s.append(")")
                }
            }
        }
        return s
    }
    
    
}
