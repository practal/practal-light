//
//  Tm.swift
//  
//
//  Created by Steven Obua on 09/08/2021.
//

import Foundation

/// Terms with DeBruijn indices
public indirect enum Tm : Hashable, Equatable {
    
    case boundvar(Int)
    
    case freevar(Var, params: [Tm])
    
    case constant(Const, binders : [Var], params: [Tm])
    
    public static func == (lhs : Tm, rhs : Tm) -> Bool {
        switch (lhs, rhs) {
        case let (.boundvar(l), .boundvar(r)): return l == r
        case let (.freevar(lv, lparams), .freevar(rv, rparams)): return lv == rv && lparams == rparams
        case let (.constant(lc, lbinders, lparams), .constant(rc, rbinders, rparams)): return lc == rc && lparams == rparams && lbinders.count == rbinders.count
        default: return false
        }
    }
    
    public func hash(into hasher: inout Hasher) {
        switch self {
        case let .boundvar(index):
            hasher.combine("b")
            hasher.combine(index)
        case let .freevar(v, params: params):
            hasher.combine("f")
            hasher.combine(v)
            for p in params {
                hasher.combine(p)
            }
        case let .constant(c, binders: binders, params: params):
            hasher.combine("c")
            hasher.combine(c)
            hasher.combine(binders.count)
            for p in params {
                hasher.combine(p)
            }
        }
    }
    
}
