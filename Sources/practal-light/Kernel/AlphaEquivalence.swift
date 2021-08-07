//
//  AlphaEquivalence.swift
//  
//
//  Created by Steven Obua on 07/08/2021.
//

import Foundation

extension KernelContext {
    
    public func alpha_equivalent(_ u : Term, _ v : Term) -> Bool {
        func equiv(boundVars1 : [Var : Var], boundVars2 : [Var : Var], _ t1 : Term, _ t2 : Term) -> Bool {
            switch (t1, t2) {
            case let (.variable(v1, params: params1), .variable(v2, params: params2)):
                if let w2 = boundVars1[v1] {
                    guard let w1 = boundVars2[v2] else { return false }
                    guard w2 == v2 && w1 == v1 else { return false }
                    guard params1.count == 0 && params2.count == 0 else { return false }
                } else {
                    guard boundVars2[v2] == nil && v1 == v2 else { return false }
                    guard params1.count == params2.count else { return false }
                }
                for (i, param) in params1.enumerated() {
                    guard equiv(boundVars1: boundVars1, boundVars2: boundVars2, param, params2[i]) else { return false }
                }
                return true
            case let (.constant(c1, binders: binders1, params: params1), .constant(c2, binders: binders2, params: params2)):
                guard c1 == c2, let head = constants[c1]?.head else { return false }
                guard head.checkShape(binders1, params1), head.checkShape(binders2, params2) else { return false }
                for (i, param) in params1.enumerated() {
                    let select1 = head.selectBoundVars(param: i, binders: binders1)
                    let select2 = head.selectBoundVars(param: i, binders: binders2)
                    var boundVars1 = boundVars1
                    var boundVars2 = boundVars2
                    for (j, b1) in select1.enumerated() {
                        let b2 = select2[j]
                        boundVars1[b1] = b2
                        boundVars2[b2] = b1
                    }
                    guard equiv(boundVars1: boundVars1, boundVars2: boundVars2, param, params2[i]) else { return false }
                }
                return true
            default:
                return false
            }
        }
        return equiv(boundVars1: [:], boundVars2: [:], u, v)
    }
    
    public func alpha_equivalent(_ u : Prop, _ v : Prop) -> Bool {
        guard u.hyps.count == v.hyps.count else { return false }
        guard u.concls.count == v.concls.count else { return false }
        for (i, hyp) in u.hyps.enumerated() {
            guard alpha_equivalent(hyp, v.hyps[i]) else { return false }
        }
        for (i, concl) in u.concls.enumerated() {
            guard alpha_equivalent(concl, v.concls[i]) else { return false }
        }
        return true
    }
    
}
