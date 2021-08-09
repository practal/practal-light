//
//  Tm.swift
//  
//
//  Created by Steven Obua on 09/08/2021.
//

import Foundation

/// Terms with DeBruijn indices
public indirect enum Tm : Hashable, Equatable {
    
    case bound(Int)
    
    case free(Var, params: [Tm])
    
    case const(Const, binders : [Var], params: [Tm])
    
    public static func == (lhs : Tm, rhs : Tm) -> Bool {
        switch (lhs, rhs) {
        case let (.bound(l), .bound(r)): return l == r
        case let (.free(lv, lparams), .free(rv, rparams)): return lv == rv && lparams == rparams
        case let (.const(lc, lbinders, lparams), .const(rc, rbinders, rparams)): return lc == rc && lparams == rparams && lbinders.count == rbinders.count
        default: return false
        }
    }
    
    public func hash(into hasher: inout Hasher) {
        switch self {
        case let .bound(index):
            hasher.combine("b")
            hasher.combine(index)
        case let .free(v, params: params):
            hasher.combine("f")
            hasher.combine(v)
            for p in params {
                hasher.combine(p)
            }
        case let .const(c, binders: binders, params: params):
            hasher.combine("c")
            hasher.combine(c)
            hasher.combine(binders.count)
            for p in params {
                hasher.combine(p)
            }
        }
    }
    
    /// If `term` is wellformed in `kc`, returns the corresponding De Bruijn term, otherwise returns `nil`
    public static func fromWellformedTerm(_ kc : KernelContext, term : Term) -> Tm? {
        
        func boundIndex(boundVars : [Var], _ v : Var) -> Int? {
            guard let i = boundVars.lastIndex(of: v) else { return nil }
            return boundVars.count - 1 - i
        }
        
        func from(boundVars : [Var], term : Term) -> Tm? {
            switch term {
            case let .variable(v, params: params):
                if let index = boundIndex(boundVars: boundVars, v) {
                    guard params.isEmpty else { return nil }
                    return .bound(index)
                } else {
                    var pms : [Tm] = []
                    for p in params {
                        guard let tm = from(boundVars: boundVars, term: p) else { return nil }
                        pms.append(tm)
                    }
                    return .free(v, params: pms)
                }
            case let .constant(c, binders: binders, params: params):
                guard let head = kc.constants[c]?.head else { return nil }
                guard head.checkShape(binders, params) else { return nil }
                var pms : [Tm] = []
                for (i, p) in params.enumerated() {
                    let selected = head.selectBoundVars(param: i, binders: binders)
                    guard let tm = from(boundVars: boundVars + selected, term: p) else { return nil }
                    pms.append(tm)
                }
                return .const(c, binders: binders, params: pms)
            }
        }
        
        return from(boundVars: [], term: term)
    }
    
    public func collectFreeVars(_ vars : inout Set<Var>) {
        switch self {
        case .bound: break
        case let .free(v, params: params):
            vars.insert(v)
            for p in params {
                p.collectFreeVars(&vars)
            }
        case let .const(_, binders: _, params: params):
            for p in params {
                p.collectFreeVars(&vars)
            }
        }
    }
    
    public func freeVars() -> Set<Var> {
        var vars : Set<Var> = []
        collectFreeVars(&vars)
        return vars
    }
    
    /// Returns a term with name binders which is equivalent to this De Bruijn term.
    /// The returned term is guaranteed to be wellformed in `kc` if this term is, otherwis `nil` is returned.
    /// The returned term does not contain any shadowed bound variables.
    public func wellformedTerm(_ kc : KernelContext) -> Term? {
        
        let frees = freeVars()
        
        func conv(boundVars : [Var], tm : Tm) -> Term? {
            
            func fresh(_ binders : [Var]) -> [Var] {
                var freshBinders : [Var] = []
                for b in binders {
                    var v = b
                    while frees.contains(v) || boundVars.contains(v) || freshBinders.contains(v) {
                        v = v.increment()
                    }
                    freshBinders.append(v)
                }
                return freshBinders
            }
            
            switch tm {
            case let .bound(index):
                if index < boundVars.count {
                    return .variable(boundVars[boundVars.count - 1 - index], params: [])
                } else {
                    return nil
                }
            case let .free(v, params: pms):
                var params : [Term] = []
                for p in pms {
                    guard let term = conv(boundVars: boundVars, tm: p) else { return nil }
                    params.append(term)
                }
                return .variable(v, params: params)
            case let .const(c, binders: binders, params: pms):
                guard let head = kc.constants[c]?.head else { return nil }
                guard binders.count == head.binders.count && pms.count == head.params.count else { return nil }
                let binders = fresh(binders)
                var params : [Term] = []
                for (i, p) in pms.enumerated() {
                    let selected = head.selectBoundVars(param: i, binders: binders)
                    guard let t = conv(boundVars: boundVars + selected, tm: p) else { return nil }
                    params.append(t)
                }
                return .constant(c, binders: binders, params: params)
            }
        }
        
        return conv(boundVars: [], tm: self)
        
    }
    
}
