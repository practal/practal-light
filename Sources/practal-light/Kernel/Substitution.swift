//
//  Substitution.swift
//  
//
//  Created by Steven Obua on 07/08/2021.
//

import Foundation

public struct TermWithHoles {
    
    public let holes : [Var]
    
    public let term : Term
    
    public init(_ holes : [Var], _ term : Term) {
        self.holes = holes
        self.term = term
    }

}

public typealias Substitution = [Var : TermWithHoles]

extension KernelContext {
    
/*
    
    public func substitute(_ substitution : Substitution, in term : Term) -> Term? {
        
        
        
        func substMultiple(boundVars : Set<Var>, terms : [Term]) -> [Term]? {
            var result : [Term] = []
            for t in terms {
                guard let s = subst(boundVars: boundVars, term: t) else { return nil }
                result.append(s)
            }
            return result
        }
        func subst(boundVars : Set<Var>, term : Term) -> Term? {
            switch term {
            case let .variable(v, params: params):
                guard !boundVars.contains(v) else { return term }
                guard let params = substMultiple(boundVars: boundVars, terms: params) else { return nil }
                if let termWithHoles = substitution[v] {
                    guard termWithHoles.holes.count == params.count else { return nil }
                    subst
                } else {
                    return .variable(v, params: params)
                }
            case let .constant(c, binders: binders, params: params):
                fatalError()
            }
        }
        return subst(boundVars: [], term: term)
    }
    
    */
}
