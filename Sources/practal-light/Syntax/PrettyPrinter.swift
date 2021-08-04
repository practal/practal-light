//
//  PrettyPrinter.swift
//  
//
//  Created by Steven Obua on 04/08/2021.
//

import Foundation

public final class PrettyPrinter {
    
    public enum Priority {
        case Atomic
        case Level(Float)
    }
    
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
    
    public func printAsTree(_ term : Term) -> Tree {
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
            return printRaw(const: const, binders: binders, params: params)
        }
    }
    
    public func print(_ term : Term) -> String {
        let tree = printAsTree(term)
        return printTree(tree)
    }

    public func printTree(_ tree : Tree) -> String {
        var s : String = ""
        for f in tree.fragments {
            switch f {
            case let .Const(c): s.append(c.id)
            case let .Var(v): s.append(v.id)
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
