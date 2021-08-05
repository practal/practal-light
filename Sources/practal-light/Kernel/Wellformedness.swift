//
//  Wellformedness.swift
//  
//
//  Created by Steven Obua on 05/08/2021.
//

import Foundation

extension Kernel {
    
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
                guard let head = defOf(const)?.head else {
                    return false
                }
                guard binders.count == head.binders.count else { return false }
                guard binders.count == Set(binders).count else { return false }
                guard params.count == head.params.count else { return false }
                for (i, p) in params.enumerated() {
                    var boundVars = boundVars
                    boundVars.formUnion(head.selectBoundVars(param : i, binders : binders))
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
    
}
