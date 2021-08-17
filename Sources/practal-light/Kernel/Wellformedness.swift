//
//  Wellformedness.swift
//  
//
//  Created by Steven Obua on 05/08/2021.
//

import Foundation

extension KernelContext {
    
    public func checkWellformedness(_ term : Term) -> (vars: [Var], arity: [Var : Int])? {
        var vars : [Var] = []
        var arity : [Var : Int] = [:]
        func check(boundVars : Set<Var>, term : Term) -> Bool {
            switch term {
            case let .variable(v, params: params):
                guard !boundVars.contains(v) else {
                    return params.isEmpty
                }
                if let a = arity[v] {
                    return a == params.count
                } else {
                    arity[v] = params.count
                    vars.append(v)
                }
                for p in params {
                    guard check(boundVars: boundVars, term: p) else { return false }
                }
                return true
            case let .constant(const, binders: binders, params: params):
                guard let head = constants[const]?.head else {
                    return false
                }
                guard head.checkShape(binders, params) else { return false }
                for (i, p) in params.enumerated() {
                    var boundVars = boundVars
                    boundVars.formUnion(head.selectBoundVars(param : i, binders : binders))
                    guard check(boundVars: boundVars, term: p) else { return false }
                }
                return true
            }
        }
        if check(boundVars: [], term: term) {
            return (vars: vars, arity: arity)
        } else {
            return nil
        }
    }
    
    public func isWellformed(_ term : Term) -> Bool {
        return checkWellformedness(term) != nil
    }
        
    /// This is only guaranteed to work for wellformed terms, otherwise the result is unspecified.
    public func freeVarsOf(_ term : Term) -> (vars : [Var], arity : [Var : Int]) {
        return checkWellformedness(term) ?? (vars: [], arity: [:])
    }
    
}
