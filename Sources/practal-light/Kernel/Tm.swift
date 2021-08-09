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
    
}

extension Tm : CustomStringConvertible {
    
    public var description: String {
        switch self {
        case let .bound(index):
            return "$\(index.description)"
        case let .free(v, params: params):
            if params.isEmpty {
                return v.description
            } else {
                let ps = params.map { p in p.description }
                return "\(v)[\(ps.joined(separator: ", "))]"
            }
        case let .const(c, binders: binders, params: params):
            let prefix = ([c.description] + binders.map { v in v.description }).joined(separator: " ")
            let ps : [String] = params.map { p in p.description }
            return "(" + ([prefix + "."] + ps).joined(separator: " ") + ")"
        }
    }

}

extension Tm {
    
    /// If `term` is wellformed in `kc`, returns the corresponding De Bruijn term, otherwise returns `nil`.
    public static func fromWellformedTerm(_ kc : KernelContext, term : Term) -> Tm? {
                
        func from(level : Int, boundVars : [Var : Int], term : Term) -> Tm? {
            switch term {
            case let .variable(v, params: params):
                if let index = boundVars[v] {
                    guard params.isEmpty else { return nil }
                    return .bound(index + level)
                } else {
                    var pms : [Tm] = []
                    for p in params {
                        guard let tm = from(level: level, boundVars: boundVars, term: p) else { return nil }
                        pms.append(tm)
                    }
                    return .free(v, params: pms)
                }
            case let .constant(c, binders: binders, params: params):
                guard let head = kc.constants[c]?.head else { return nil }
                guard head.checkShape(binders, params) else { return nil }
                var pms : [Tm] = []
                let sublevel = level + binders.count
                for (i, p) in params.enumerated() {
                    let selected = head.selectBoundVars(param: i, binders: binders)
                    var boundVars = boundVars
                    for v in selected {
                        let index = binders.count - 1 - binders.firstIndex(of: v)!
                        boundVars[v] = index - sublevel
                    }
                    guard let tm = from(level: sublevel, boundVars: boundVars, term: p) else { return nil }
                    pms.append(tm)
                }
                return .const(c, binders: binders, params: pms)
            }
        }
        
        return from(level: 0, boundVars: [:], term: term)
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
    /// The returned term is guaranteed to be wellformed in any KernelContext in which this term is wellformed.
    /// If there are dangling bound variables, `nil` is returned.
    public func term() -> Term? {
        
        let frees = freeVars()
        
        func convMultiple(boundVars : [Var], _ tms : [Tm]) -> [Term]? {
            let terms = tms.compactMap { tm in conv(boundVars: boundVars, tm) }
            guard terms.count == tms.count else { return nil }
            return terms
        }
        
        func conv(boundVars : [Var], _ tm : Tm) -> Term? {
            
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
                if index >= 0 && index < boundVars.count {
                    return .variable(boundVars[boundVars.count - 1 - index], params: [])
                } else {
                    return nil
                }
            case let .free(v, params: pms):
                guard let params : [Term] = convMultiple(boundVars: boundVars, pms) else { return nil }
                return .variable(v, params: params)
            case let .const(c, binders: binders, params: pms):
                let binders = fresh(binders)
                guard let params = convMultiple(boundVars: boundVars + binders, pms) else { return nil }
                return .constant(c, binders: binders, params: params)
            }
        }
        
        return conv(boundVars: [], self)
        
    }
    
    // Adjusts all dangling (according to `level`) bound variables  by `delta`.
    public func adjust(level : Int, delta : Int) -> Tm {
        switch self {
        case let .bound(index):
            if index < level { return self }
            else { return .bound(index + delta) }
        case let .free(v, params: params):
            let sparams = params.map { p in p.adjust(level: level, delta: delta) }
            return .free(v, params: sparams)
        case let .const(c, binders: binders, params: params):
            let sublevel = level + binders.count
            let sparams = params.map { p in p.adjust(level: sublevel, delta: delta) }
            return .const(c, binders: binders, params: sparams)
        }
    }
    
}

extension KernelContext {
    
    public func tmOf(_ term : Term) -> Tm? {
        return Tm.fromWellformedTerm(self, term: term)
    }
    
    public func alpha_equivalent(_ u : Term, _ v : Term) -> Bool {
        guard let u = tmOf(u) else { return false }
        guard let v = tmOf(v) else { return false }
        return u == v
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
