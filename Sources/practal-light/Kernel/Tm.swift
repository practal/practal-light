//
//  Tm.swift
//  
//
//  Created by Steven Obua on 09/08/2021.
//

import Foundation

/// Terms with DeBruijn indices
public indirect enum Tm : Hashable, Equatable, Comparable {
    
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
        
    public static func compare(_ params1: [Tm], _ params2: [Tm]) -> Int {
        guard params1.count == params2.count else {
            return params1.count < params2.count ? -1 : 1
        }
        for (i, p1) in params1.enumerated() {
            let p2 = params2[i]
            let c = compare(p1, p2)
            guard c == 0 else { return c }
        }
        return 0
    }
    
    public static func compare(_ lhs: Tm, _ rhs: Tm) -> Int {
        switch (lhs, rhs) {
        case let (.bound(index1), .bound(index2)):
            if index1 < index2 { return -1 }
            else { return index1 == index2 ? 0 : 1 }
        case let (.const(c1, binders1, params1), .const(c2, binders2, params2)):
            guard c1 == c2 else {
                return c1.name.id < c2.name.id ? -1 : 1
            }
            guard binders1.count == binders2.count else {
                return binders1.count < binders2.count ? -1 : 1
            }
            return compare(params1, params2)
        case let (.free(v1, params1), .free(v2, params2)):
            guard v1 == v2 else {
                return v1 < v2 ? -1 : 1
            }
            return compare(params1, params2)
        case (.bound, _): return -1
        case (_, .bound): return 1
        case (.const, _): return -1
        case (_, .const): return 1
        }
    }
    
    public static func < (lhs: Tm, rhs: Tm) -> Bool {
        return compare(lhs, rhs) < 0
    }
    
    public var size : Int {
        switch self {
        case .bound: return 1
        case let .free(_, params: params):
            var s = 1
            for p in params { s += p.size }
            return s
        case let .const(_, binders: _, params: params):
            var s = 1
            for p in params { s += p.size }
            return s
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
                
        var frees = FreeVars()
        
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
                    guard frees.add(v, arity: pms.count) else { return nil }
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
                        let index = binders.firstIndex(of: v)!
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
    
    public func freeVars() -> Set<Var> {
        return FreeVars(self).vars
    }
    
    public func freeVarsWithArity() -> [Var : Int]? {
        var frees = FreeVars()
        guard frees.add(self) else { return nil }
        return frees.arities
    }
    
    /// Returns a term with name binders which is equivalent to this De Bruijn term.
    /// The returned term is guaranteed to be wellformed in any KernelContext in which this term is wellformed.
    /// If there are dangling bound variables, `nil` is returned.
    /// `nil` may also be returned if the term is not wellformed, but this cannot be relied upon.
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
                guard let params = convMultiple(boundVars: boundVars + binders.reversed(), pms) else { return nil }
                return .constant(c, binders: binders, params: params)
            }
        }
        
        return conv(boundVars: [], self)
        
    }
    
    // Adjusts all dangling (according to `level`) bound variables  by `delta`.
    public func incrementDangling(level : Int, delta : Int) -> Tm {
        guard delta >= 0 else { fatalError() }
        switch self {
        case let .bound(index):
            if index < level { return self }
            else { return .bound(index + delta) }
        case let .free(v, params: params):
            let sparams = params.map { p in p.incrementDangling(level: level, delta: delta) }
            return .free(v, params: sparams)
        case let .const(c, binders: binders, params: params):
            let sublevel = level + binders.count
            let sparams = params.map { p in p.incrementDangling(level: sublevel, delta: delta) }
            return .const(c, binders: binders, params: sparams)
        }
    }
    
    public func toZeroLevel(level : Int) -> Tm? {
        switch self {
        case let .bound(index):
            if index < level { return nil }
            else { return .bound(index - level) }
        case let .free(v, params: params):
            let sparams = params.compactMap { p in p.toZeroLevel(level: level) }
            guard sparams.count == params.count else { return nil }
            return .free(v, params: sparams)
        case let .const(c, binders: binders, params: params):
            let sublevel = level + binders.count
            let sparams = params.compactMap { p in p.toZeroLevel(level: sublevel) }
            guard sparams.count == params.count else { return nil }
            return .const(c, binders: binders, params: sparams)
        }
    }
    
    public func occursForSure(_ v : Var) -> Bool {
        switch self {
        case .bound: return false
        case let .free(w, params: _): return w == v
        case let .const(_, binders: _, params: params):
            for p in params {
                if p.occursForSure(v) { return true }
            }
            return false
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
        
    public func isWellformed(level : Int, _ tm : Tm, _ frees : inout FreeVars) -> Bool {
        
        func check(level : Int, accessible : [Bool], _ tm : Tm) -> Bool {
            switch tm {
            case let .bound(v):
                guard v < level else { return false }
                return accessible[v]
            case let .free(v, params: params):
                guard frees.add(v, arity: params.count) else { return false}
                return  params.allSatisfy { p in check(level: level, accessible: accessible, p) }
            case let .const(c, binders: binders, params: params):
                guard let head = constants[c]?.head else { return false }
                guard head.binders.count == binders.count && head.params.count == params.count else { return false }
                let sublevel = level + binders.count
                for (i, p) in params.enumerated() {
                    guard check(level: sublevel, accessible: accessible + head.accessible(param: i).reversed(), p) else { return false }
                }
                return true
            }
        }
        
        return check(level : level, accessible : [Bool](repeating: true, count: level), tm)
    }

}
