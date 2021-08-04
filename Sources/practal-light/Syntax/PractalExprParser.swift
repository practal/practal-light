//
//  PractalExprParser.swift
//
//  Created by Steven Obua on 26/07/2021.
//

import Foundation
import ParsingKit
import FirstOrderDeepEmbedding

public class PractalExprParser {
    
    public let grammar : PractalExprGrammar
    public let parser : Parser<Character>
    public let patterns : [(SyntaxPattern, [ConcreteSyntax])]
    private let patternLookup : [String : (syntaxPattern : Int, concreteSyntax : Int)]
    
    public init(patterns : [(SyntaxPattern, [ConcreteSyntax])] = []) {
        self.grammar = PractalExprGrammar(patterns: patterns)
        self.parser = grammar.parser()
        self.patterns = patterns
        self.patternLookup = PractalExprParser.makePatternLookup(patterns : patterns)
    }
    
    private static func makePatternLookup(patterns : [(SyntaxPattern, [ConcreteSyntax])]) -> [String : (syntaxPattern : Int, concreteSyntax : Int)] {
        var lookup : [String : (syntaxPattern : Int, concreteSyntax : Int)] = [:]
        for (i, (_, css)) in patterns.enumerated() {
            for cs in 0 ..< css.count {
                let name = PractalExprGrammar.syntaxPatternNonterminalName(patternIndex: i, concreteSyntax: cs)
                lookup[name] = (syntaxPattern: i, concreteSyntax: cs)
            }
        }
        return lookup
    }
    
    public func parse(expr : String) -> Set<Term> {
        switch parser.parse(input: expr, position: 0, start: grammar.PractalExpr) {
        case let .failed(position):
            print("parsing failed at position: \(position)")
            return []
        case let .success(length: length, results: results):
            guard length == expr.count else {
                print("could not parse all, only \(length) characters")
                return []
            }
            guard let parseTree = results[UNIT.singleton] else {
                print("no result found")
                return []
            }
            guard let parseTree = parseTree else {
                print("the parseTree is nil")
                return []
            }
            let tree = SyntaxTree.from(parseTree: parseTree, grammar: grammar)
            let trees = tree.explode()
            return Set(convert(expr: expr, syntaxTrees: Array(trees)))
        }
    }
    
    public func parse(css : String) -> ConcreteSyntax? {
        switch parser.parse(input: css, position: 0, start: grammar.ConcreteSyntaxSpec) {
        case let .failed(position):
            print("parsing failed at position: \(position)")
            return nil
        case let .success(length: length, results: results):
            guard length == css.count else {
                print("could not parse all, only \(length) characters")
                return nil
            }
            guard let parseTree = results[UNIT.singleton] else {
                print("no result found")
                return nil
            }
            guard let parseTree = parseTree else {
                print("the parseTree is nil")
                return nil
            }
            let tree = SyntaxTree.from(parseTree: parseTree, grammar: grammar)
            let trees = tree.explode()
            guard trees.count == 1 else {
                return nil
            }
            return convert(css: css, syntaxTree: trees.first!, priority: .None)
        }

    }
    
    public func convert(expr input : String, syntaxTrees : [SyntaxTree]) -> [Term] {
        let PRACTAL_EXPR = "\(grammar.PractalExpr)"
        let VARIABLE = "\(grammar.Variable)"
        let CONSTANT = "\(grammar.Constant)"
        let VAR = "\(grammar.Var)"
        let CONST = "\(grammar.Const)"
        let VARLIST = "\(grammar.VarList)"
        let EXPRLIST = "\(grammar.ExprList)"
        let EXPRCOMMALIST = "\(grammar.ExprCommaList)"
        
        let input = Array(input)

        func check(_ syntaxTree : SyntaxTree, symbol : String) {
            guard syntaxTree.symbol == symbol else {
                fatalError("syntax tree should be '\(symbol)', but '\(syntaxTree.symbol)' found")
            }
        }
        
        func textOf(_ syntaxTree : SyntaxTree) -> String {
            return String(input[syntaxTree.from ..< syntaxTree.to])
        }
        
        func varOf(_ syntaxTree : SyntaxTree) -> Var {
            check(syntaxTree, symbol: VAR)
            return Var(primed: textOf(syntaxTree))!
        }
        
        func constOf(_ syntaxTree : SyntaxTree) -> Const {
            check(syntaxTree, symbol: CONST)
            let t = textOf(syntaxTree)
            return Const(qualified: t)!
        }
        
        func varListOf(_ syntaxTree : SyntaxTree) -> [Var] {
            check(syntaxTree, symbol: VARLIST)
            return syntaxTree.children.map(varOf)
        }
        
        func exprListOf(_ syntaxTree : SyntaxTree) -> [Term] {
            check(syntaxTree, symbol: EXPRLIST)
            return syntaxTree.children.map(conv)
        }
                
        func exprCommaListOf(_ syntaxTree : SyntaxTree) -> [Term] {
            check(syntaxTree, symbol: EXPRCOMMALIST)
            return syntaxTree.children.map(conv)
        }

        func convConcrete(pattern : SyntaxPattern, concreteSyntax : ConcreteSyntax, _ syntaxTree : SyntaxTree) -> Term {
            var terms : [Var : Term] = [:]
            var binders : [Var : Var] = [:]
            for (i, v) in concreteSyntax.vars.enumerated() {
                if pattern.containsBinder(v) {
                    let w = varOf(syntaxTree[i])
                    binders[v] = w
                } else {
                    terms[v] = conv(syntaxTree[i])
                }
            }
            return pattern.instantiate(binders, terms)
        }
                
        func conv(_ syntaxTree : SyntaxTree) -> Term {
            switch (syntaxTree.symbol, syntaxTree.children.count) {
            case (PRACTAL_EXPR, 1): return conv(syntaxTree.children[0])
            case (VARIABLE, 1): return .variable(varOf(syntaxTree[0]), params: [])
            case (VARIABLE, 2):
                let v = varOf(syntaxTree[0])
                let params = exprCommaListOf(syntaxTree[1])
                return .variable(v, params: params)
            case (CONSTANT, 3):
                let c = constOf(syntaxTree[0])
                let binders = varListOf(syntaxTree[1])
                let params = exprListOf(syntaxTree[2])
                return .constant(c, binders: binders, params: params)
            case let (symbol, arity):
                guard let pattern = patternLookup[symbol] else {
                    fatalError("cannot convert symbol '\(symbol)' with arity \(arity)")
                }
                let p = patterns[pattern.syntaxPattern]
                let concreteSyntax = p.1[pattern.concreteSyntax]
                return convConcrete(pattern: p.0, concreteSyntax: concreteSyntax, syntaxTree)
            }
        }
        
        return syntaxTrees.map(conv)
    }
    
    public func convert(css input : String, syntaxTree : SyntaxTree, priority : ConcreteSyntax.Priority) -> ConcreteSyntax? {
        let CSS = "\(grammar.ConcreteSyntaxSpec)"
        let CSF_VAR = "\(grammar.CSF_Var)"
        let CSF_RAISED_VAR = "\(grammar.CSF_RaisedVar)"
        let CSF_TEXT = "\(grammar.CSF_Text)"
        let CSF_SPACE = "\(grammar.CSF_Space)"
        
        let input = Array(input)

        func check(_ syntaxTree : SyntaxTree, symbol : String) {
            guard syntaxTree.symbol == symbol else {
                fatalError("syntax tree should be '\(symbol)', but '\(syntaxTree.symbol)' found")
            }
        }
        
        func textOf(_ syntaxTree : SyntaxTree) -> String {
            return String(input[syntaxTree.from ..< syntaxTree.to])
        }
        
        func csfOf(_ syntaxTree : SyntaxTree) -> ConcreteSyntax.Fragment {
            switch syntaxTree.symbol {
            case CSF_VAR: return .Var(Var(primed: textOf(syntaxTree))!, raised: false)
            case CSF_RAISED_VAR: return .Var(Var(primed: textOf(syntaxTree))!, raised: true)
            case CSF_SPACE: return .Space
            case CSF_TEXT: return .Text(textOf(syntaxTree))
            default: fatalError("don't know concrete syntax fragment '\(syntaxTree.symbol)'")
            }
        }
                        
        check(syntaxTree, symbol: CSS)
        var fragments : [ConcreteSyntax.Fragment] = []
        for child in syntaxTree.children {
            fragments.append(csfOf(child))
        }
        return ConcreteSyntax(fragments: fragments, priority: priority).normalized

    }
    
}
