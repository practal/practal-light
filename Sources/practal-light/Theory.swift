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
            fatalError("couldn't parse '\(expr)'")
        }
        return terms.first!
    }
        
    @discardableResult
    public func introduce(constant : Term) -> Const {
        fatalError()
    }
    
    @discardableResult
    public func define(constant : Term, definition : Term) -> Const {
        fatalError()
    }

    public func addSyntax(const : Const, concreteSyntax : ConcreteSyntax) {
        fatalError()
    }
    
    private func addSyntax(const : Const, syntax : [String]) {
        for s in syntax {
            guard let css = parser.parse(css: s) else {
                fatalError("could not process syntax definition: \(s)")
            }
            addSyntax(const: const, concreteSyntax: css)
        }
    }
    
    @discardableResult
    public func introduce(_ constant : String, syntax : String...) -> Const {
        let const = introduce(constant: parse(constant))
        addSyntax(const: const, syntax: Array(syntax))
        return const
    }
    
    @discardableResult
    public func define(_ constant : String, _ definition : String, syntax : String...) -> Const {
        let lhs = parse(constant)
        let rhs = parse(definition)
        let const = define(constant: lhs, definition: rhs)
        addSyntax(const: const, syntax: Array(syntax))
        return const
    }
        
}
