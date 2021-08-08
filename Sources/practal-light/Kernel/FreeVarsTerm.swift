//
//  FreeVarsTerm.swift
//  
//
//  Created by Steven Obua on 08/08/2021.
//

import Foundation

internal enum FreeVarsTerm {
    case variable(Var, params: [FreeVarsTerm], freeVars: Set<Var>)
    case const(Const, binders: [Var], params: [FreeVarsTerm], freeVars: Set<Var>)
    
    var freeVars : Set<Var> {
        switch self {
        case let .variable(_, params: _, freeVars: freeVars): return freeVars
        case let .const(_, binders: _, params: _, freeVars: freeVars): return freeVars
        }
    }
}

extension KernelContext {
    
    internal func freeVarsTermsOf(_ terms : [Term]) -> [FreeVarsTerm]? {
        var fterms : [FreeVarsTerm] = []
        for t in terms {
            guard let ft = freeVarsTermOf(t) else { return nil }
            fterms.append(ft)
        }
        return fterms
    }
    
    internal func freeVarsTermOf(_ term : Term) -> FreeVarsTerm? {
        switch term {
        case let .variable(v, params: params):
            guard let fparams = freeVarsTermsOf(params) else { return nil }
            var frees : Set<Var> = []
            for p in fparams {
                frees.formUnion(p.freeVars)
            }
            frees.insert(v)
            return .variable(v, params: fparams, freeVars: frees)
        case let .constant(c, binders: binders, params: params):
            guard let head = constants[c]?.head else { return nil }
            guard head.checkShape(binders, params) else { return nil }
            guard let fparams = freeVarsTermsOf(params) else { return nil }
            var frees : Set<Var> = []
            for (i, p) in fparams.enumerated() {
                let boundVars = head.selectBoundVars(param: i, binders: binders)
                frees.formUnion(p.freeVars.subtracting(boundVars))
            }
            return .const(c, binders: binders, params: fparams, freeVars: frees)
        }
    }
    
}


