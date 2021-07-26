//
//  Theory.swift
//  
//  Created by Steven Obua on 26/07/2021.
//

import Foundation

public final class Theory {
    
    private var _constants : [Const : ConstSyntax]
    private var _definitions : [Const : Term]
    
    private var _parser : PractalExprParser
    private var dirtyParser : Bool
    
    public init() {
        self._constants = [:]
        self._definitions = [:]
        self._parser = PractalExprParser(constants: [:])
        self.dirtyParser = false
    }
    
    private func invalidateParser() {
        dirtyParser = true
    }
    
    private var parser : PractalExprParser {
        if dirtyParser {
            _parser = PractalExprParser(constants: _constants)
            dirtyParser = false
        }
        return _parser
    }
    
    public func parseAll(_ expr : String) -> Set<Term> {
        return parser.parse(expr: expr)
    }
    
    public func parse(_ expr : String) -> Term {
        let terms = parseAll(expr)
        guard terms.count == 1 else {
            fatalError("Could not parse '\(expr)'")
        }
        return terms.first!
    }
        
    @discardableResult
    public func introduce(constant : Term) -> Const {
        switch constant {
        case .variable: fatalError("Constant to be introduced expected, but found variable '\(constant)'")
        case let .constant(c, binders: binders, params: params):
            func error(_ s : String) -> Never {
                fatalError("Cannot introduce constant '\(c)': \(s)")
            }
            guard _constants[c] == nil else { error("constant has already been introduced") }
            let binderVars = Set(binders)
            var paramVars : Set<Var> = []
            guard binderVars.count == binders.count else { error("duplicate binders") }
            for param in params {
                switch param {
                case .constant: error("parameters must be variables")
                case let .variable(v, dependencies: deps):
                    guard !binderVars.contains(v) else { error("parameter '\(v)' is already a binder") }
                    guard !paramVars.contains(v) else { error("duplicate parameter variable '\(v)'") }
                    guard deps.count == Set(deps).count else { error("duplicate dependencies") }
                    for dep in deps {
                        guard binderVars.contains(dep) else { error("dependency '\(dep)' is not a binder")}
                    }
                    paramVars.insert(v)
                }
            }
            let abstractSyntax = AbstractSyntax(const: c, binders: binders, params: params)
            let syntax = ConstSyntax(abstractSyntax: abstractSyntax, concreteSyntaxes: [])
            _constants[c] = syntax
            return c
        }
    }
    
    public func checkWellformedness(_ term : Term) -> [Var : Int]? {
        fatalError()
    }
    
    public func isWellformed(_ term : Term) -> Bool {
        return checkWellformedness(term) != nil
    }
    
    // This is guaranteed to work only for wellformed terms, otherwise the result is unspecified.
    public func freeVarsOf(_ term : Term) -> [Var : Int] {
        return checkWellformedness(term) ?? [:]
    }
    
    @discardableResult
    public func define(constant : Term, definition : Term) -> Const {
        guard let freeVarsRHS = checkWellformedness(definition) else {
            fatalError("The definition '\(definition)' is not well-formed")
        }
        let const = introduce(constant: constant)
        let lhs = _constants[const]!.abstractSyntax.term
        let freeVarsLHS = freeVarsOf(lhs)
        for (v, i) in freeVarsRHS {
            guard let j = freeVarsLHS[v], i == j else {
                fatalError("The variable '\(v)' is free and not properly bound in the definition")
            }
        }
        _definitions[const] = definition
        return const
    }

    private func addSyntax(const : Const, concreteSyntax : ConcreteSyntax) {
        fatalError()
    }
    
    public func addSyntax(const : Const, syntax : String) {
        guard let css = parser.parse(css: syntax) else {
            fatalError("Could not parse concrete syntax spec '\(syntax)'")
        }
        addSyntax(const: const, concreteSyntax: css)
    }
    
    @discardableResult
    public func introduce(_ constant : String, syntax : String...) -> Const {
        let const = introduce(constant: parse(constant))
        for s in syntax { addSyntax(const: const, syntax: s) }
        return const
    }
    
    @discardableResult
    public func define(_ constant : String, _ definition : String, syntax : String...) -> Const {
        let lhs = parse(constant)
        let rhs = parse(definition)
        let const = define(constant: lhs, definition: rhs)
        for s in syntax { addSyntax(const: const, syntax: s) }
        return const
    }
        
}
