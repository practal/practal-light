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
    public let constants : [Const : ConstSyntax]
    
    public init(constants : [Const : ConstSyntax] = [:]) {
        self.grammar = PractalExprGrammar()
        self.parser = grammar.parser()
        self.constants = constants
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
            print("There are \(trees.count) trees:")
            print("-------")
            for tree in trees {
                tree.debug()
                print("-------")
            }
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
            print("There are \(trees.count) trees:")
            print("-------")
            for tree in trees {
                tree.debug()
                print("-------")
            }
            guard trees.count == 1 else {
                return nil
            }
            return convert(css: css, syntaxTree: trees.first!)
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
            return Id(textOf(syntaxTree))!
        }
        
        func constOf(_ syntaxTree : SyntaxTree) -> Const {
            check(syntaxTree, symbol: CONST)
            return Id(textOf(syntaxTree))!
        }
        
        func varListOf(_ syntaxTree : SyntaxTree) -> [Var] {
            check(syntaxTree, symbol: VARLIST)
            return syntaxTree.children.map(varOf)
        }
        
        func exprListOf(_ syntaxTree : SyntaxTree) -> [Term] {
            check(syntaxTree, symbol: EXPRLIST)
            return syntaxTree.children.map(conv)
        }
                
        func conv(_ syntaxTree : SyntaxTree) -> Term {
            switch (syntaxTree.symbol, syntaxTree.children.count) {
            case (PRACTAL_EXPR, 1): return conv(syntaxTree.children[0])
            case (VARIABLE, 1): return .variable(varOf(syntaxTree[0]), dependencies: [])
            case (VARIABLE, 2):
                let v = varOf(syntaxTree[0])
                let deps = varListOf(syntaxTree[1])
                return .variable(v, dependencies: deps)
            case (CONSTANT, 3):
                let c = constOf(syntaxTree[0])
                let binders = varListOf(syntaxTree[1])
                let params = exprListOf(syntaxTree[2])
                return .constant(c, binders: binders, params: params)
            case let (symbol, arity): fatalError("cannot convert symbol '\(symbol)' with arity \(arity)")
            }
        }
        
        return syntaxTrees.map(conv)
    }
    
    public func convert(css input : String, syntaxTree : SyntaxTree) -> ConcreteSyntax? {
        let CSS = "\(grammar.ConcreteSyntaxSpec)"
        let CSF_VAR = "\(grammar.CSF_Var)"
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
            case CSF_VAR: return .Var(Id(textOf(syntaxTree))!)
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
        return ConcreteSyntax(fragments: fragments).normalized

    }
    
}
