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
    private var _printer : PrettyPrinter
    private var dirtySyntax : Bool
    
    public init() {
        self._constants = [:]
        self._definitions = [:]
        self._parser = PractalExprParser()
        self._printer = PrettyPrinter()
        self.dirtySyntax = false
    }
    
    public subscript(_ const : Const) -> ConstSyntax? {
        return _constants[const]
    }
    
    private func invalidateSyntax() {
        dirtySyntax = true
    }
    
    private var parser : PractalExprParser {
        refreshSyntax()
        return _parser
    }
    
    private var printer : PrettyPrinter {
        refreshSyntax()
        return _printer
    }
    
    private func refreshSyntax() {
        if dirtySyntax {
            var patterns : [(SyntaxPattern, [ConcreteSyntax])] = []
            for (_, constSyntax) in _constants {
                let p = SyntaxPattern.from(constSyntax.abstractSyntax.term)
                patterns.append((p, constSyntax.concreteSyntaxes))
            }
            _parser = PractalExprParser(patterns: patterns)
            _printer = PrettyPrinter(patterns: patterns)
            dirtySyntax = false
        }
    }
    
    public func parseAll(_ expr : String) -> Set<Term> {
        return parser.parse(expr: expr)
    }
    
    public func parse(_ expr : String) -> Term {
        let terms = parseAll(expr)
        guard terms.count == 1 else {
            if terms.count > 1 {
                print("'\(expr)' cannot be parsed in a unique way:")
                for (i, term) in terms.enumerated() {
                    print("\(i+1). '\(pretty(term))', raw: '\(term)'")
                }
            }
            fatalError("Could not parse '\(expr)'")
        }
        return terms.first!
    }
        
    // quick workaround for now to avoid excessive brackets
    private static func needsBrackets(_ s : String) -> Bool {
        if !s.contains(" ") { return false }
        guard s.starts(with: "(") else { return true }
        var opened = 1
        for c in s.dropFirst() {
            guard opened > 0 else { return true }
            if c == "(" {
                opened += 1
            } else if c == ")" {
                opened -= 1
            }
        }
        return false
    }

    internal static func wrapBrackets(_ s : String) -> String {
        if needsBrackets(s) { return "(\(s))" } else { return s }
    }
    
    public func pretty(_ expr : Term) -> String {
        return printer.print(expr)
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
                case let .variable(v, params: deps):
                    guard !binderVars.contains(v) else { error("parameter '\(v)' is already a binder") }
                    guard !paramVars.contains(v) else { error("duplicate parameter variable '\(v)'") }
                    guard deps.count == Set(deps).count else { error("duplicate dependencies") }
                    for dep in deps {
                        guard let d = dep.boundVar, binderVars.contains(d) else { error("dependency '\(dep)' is not a binder")}
                    }
                    paramVars.insert(v)
                }
            }
            let abstractSyntax = AbstractSyntax(const: c, binders: binders, params: params)
            let syntax = ConstSyntax(abstractSyntax: abstractSyntax, concreteSyntaxes: [])
            _constants[c] = syntax
            invalidateSyntax()
            return c
        }
    }
    
    public func checkWellformedness(_ term : Term) -> [Var : Int]? {
        var freeVars : [Var : Int] = [:]
        func check(boundVars : Set<Var>, term : Term) -> Bool {
            switch term {
            case let .variable(v, params: params):
                guard !boundVars.contains(v) else {
                    return params.isEmpty
                }
                for p in params {
                    guard check(boundVars: boundVars, term: p) else { return false }
                }
                if let arity = freeVars[v] {
                    return arity == params.count
                } else {
                    freeVars[v] = params.count
                }
                return true
            case let .constant(const, binders: binders, params: params):
                guard let abstractSyntax = _constants[const]?.abstractSyntax else {
                    return false
                }
                guard binders.count == abstractSyntax.binders.count else { return false }
                guard binders.count == Set(binders).count else { return false }
                guard params.count == abstractSyntax.params.count else { return false }
                for (i, p) in params.enumerated() {
                    var boundVars = boundVars
                    boundVars.formUnion(abstractSyntax.selectBoundVars(param : i, binders : binders))
                    guard check(boundVars: boundVars, term: p) else { return false }
                }
                return true
            }
        }
        if check(boundVars: [], term: term) {
            return freeVars
        } else {
            return nil
        }
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
        let freeVarsLHS = _constants[const]!.abstractSyntax.freeVars
        for (v, i) in freeVarsRHS {
            guard let j = freeVarsLHS[v], i == j else {
                fatalError("The variable '\(v)' is free and not properly bound in the definition")
            }
        }
        _definitions[const] = definition
        invalidateSyntax()
        return const
    }

    private func addSyntax(const : Const, concreteSyntax : ConcreteSyntax) {
        func error(_ s : String) -> Never {
            fatalError("Cannot add syntax to constant '\(const)': \(s)")
        }
        guard let syntax = _constants[const] else {
            error("no such constant exists")
        }
        let vars = syntax.abstractSyntax.allVars
        let concreteSyntax = concreteSyntax.selectVars { v in vars[v] != nil }
        guard !concreteSyntax.hasDuplicateVarOccurrences else {
            error("duplicate free variables found in the concrete syntax")
        }
        guard Set(concreteSyntax.vars).count == vars.count else {
            error("some free variables of the abstract syntax do not occur in the concrete syntax")
        }
        var newSyntax = syntax
        newSyntax.append(concreteSyntax)
        _constants[const] = newSyntax
        invalidateSyntax()
    }
    
    public func addSyntax(const : Const, syntax : String, priority : Float? = nil) {
        guard let css = parser.parse(css: syntax) else {
            fatalError("Could not parse concrete syntax spec '\(syntax)'")
        }
        addSyntax(const: const, concreteSyntax: css.withPriority(priority))
    }
    
    @discardableResult
    public func introduce(_ constant : String, syntax : String..., priority : Float? = nil) -> Const {
        let const = introduce(constant: parse(constant))
        for s in syntax { addSyntax(const: const, syntax: s, priority: priority) }
        return const
    }
    
    @discardableResult
    public func define(_ constant : String, _ definition : String, syntax : String..., priority : Float? = nil) -> Const {
        let lhs = parse(constant)
        let rhs = parse(definition)
        let const = define(constant: lhs, definition: rhs)
        for s in syntax { addSyntax(const: const, syntax: s, priority: priority) }
        return const
    }
        
}
