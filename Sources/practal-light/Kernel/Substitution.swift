//
//  Substitution.swift
//  
//
//  Created by Steven Obua on 09/08/2021.
//

import Foundation

public struct TermWithHoles {
    
    public let holes : [Var]
    
    public let term : Term
    
    public init(_ holes : [Var], _ term : Term) {
        guard Set(holes).count == holes.count else { fatalError() }
        self.holes = holes
        self.term = term
    }

}

public typealias Substitution = [Var : TermWithHoles]

public struct TmWithHoles {
    
    public let holes : Int
    
    public let tm : Tm
    
    public init(holes : Int = 0, _ tm : Tm) {
        self.holes = holes
        self.tm = tm
    }
    
    public init?(_ kc : KernelContext, wellformed termWithHoles : TermWithHoles) {
        guard let tm = Tm.fromWellformedTerm(kc, term: termWithHoles.term) else { return nil }
        var subst = TmSubstitution()
        holes = termWithHoles.holes.count
        for (i, v) in termWithHoles.holes.enumerated() {
            subst[v] = TmWithHoles(.bound(i))
        }
        if let tm = subst.apply(tm) {
            self.tm = tm
        } else {
            return nil
        }
    }
    
    public func fillHoles() -> Tm? {
        guard holes == 0 else { return nil }
        return tm
    }
    
    public func fillHoles(_ params : [Tm]) -> Tm? {
        guard params.count == holes else { return nil }
        var subst = TmSubstitution()
        for (i, p) in params.enumerated() {
            subst[i] = TmWithHoles(p)
        }
        return subst.apply(level: params.count, tm)
    }
    
    public static func projection(holes : Int, _ k : Int) -> TmWithHoles {
        return TmWithHoles(holes: holes, .bound(k))
    }
    
    public static func constant(holes : Int, _ bound : Int) -> TmWithHoles {
        return TmWithHoles(holes: holes, .bound(bound + holes))
    }
    
    public static func constant(holes : Int, head : Head, fresh : (Var) -> Var) -> TmWithHoles {
        var params : [Tm] = []
        let binders = head.binders
        let level = binders.count
        let holeArgs = (level ..< level + holes).map { i in Tm.bound(i)}
        for (i, p) in head.params.enumerated() {
            let selected = head.selectBoundVars(param: i, binders: binders)
            let args : [Tm] = selected.map { b in Tm.bound(head.binderIndex(b)!) }
            let F = Tm.free(fresh(p.var!), params: args + holeArgs)
            params.append(F)
        }
        let tm = Tm.const(head.const, binders: binders, params: params)
        return TmWithHoles(holes: holes, tm)
    }
    
    public static func variable(holes : Int, `var` v: Var, numargs : Int, fresh : (Var) -> Var) -> TmWithHoles {
        var params : [Tm] = []
        let holeArgs = (0 ..< holes).map { i in Tm.bound(i)}
        for k in 0 ..< numargs {
            let name = "\(v.name.id)-arg-\(k)"
            let p = Tm.free(Var(name)!, params: holeArgs)
            params.append(p)
        }
        let tm = Tm.free(v, params: params)
        return TmWithHoles(holes: holes, tm)
    }

}

public struct TmSubstitution {
    
    private var free : [Var : TmWithHoles]
    private var bound : [Int : TmWithHoles]
    
    public init(free : [Var : TmWithHoles] = [:], bound : [Int : TmWithHoles] = [:]) {
        self.free = free
        self.bound = bound
    }
    
    public init?(_ kc : KernelContext, wellformed substitution : Substitution) {
        bound = [:]
        free = [:]
        for (v, t) in substitution {
            guard let twh = TmWithHoles(kc, wellformed: t) else { return nil }
            free[v] = twh
        }
    }
    
    public mutating func restrict(_ vars : Set<Var>) {
        free = free.filter { (v, _) in vars.contains(v) }
    }
    
    public subscript(_ index : Int) -> TmWithHoles? {
        get {
            return bound[index]
        }
        
        set {
            bound[index] = newValue
        }
    }

    public subscript(_ v : Var) -> TmWithHoles? {
        get {
            return free[v]
        }
        
        set {
            free[v] = newValue
        }
    }

    public var isEmpty : Bool {
        return free.isEmpty && bound.isEmpty
    }
    
    public func apply(level : Int = 0, _ tms : [Tm]) -> [Tm]? {
        guard !isEmpty else { return tms }
        return app(level: level, tms)
    }
    
    public func apply(level : Int = 0, _ tm : Tm) -> Tm? {
        guard !isEmpty else { return tm }
        return app(level: level, tm)
    }
    
    public func apply(_ tm : TmWithHoles) -> TmWithHoles? {
        guard let s = apply(level: tm.holes, tm.tm) else { return nil }
        return TmWithHoles(holes: tm.holes, s)
    }
    
    public mutating func compose(_ subst : TmSubstitution) -> Bool {
        var newFree : [Var : TmWithHoles] = [:]
        var newBound : [Int : TmWithHoles] = [:]
        for (v, t) in free {
            guard let s = subst.apply(t) else { return false }
            newFree[v] = s
        }
        for (i, t) in bound {
            guard let s = subst.apply(t) else { return false }
            newBound[i] = s
        }
        free = newFree
        bound = newBound
        return true
    }
    
    private func app(level : Int, _ tms : [Tm]) -> [Tm]? {
        let stms = tms.compactMap { tm in app(level: level, tm) }
        guard stms.count == tms.count else { return nil }
        return stms
    }
    
    private func app(level : Int, _ tm : Tm) -> Tm? {
        switch tm {
        case let .bound(index):
            if index >= level, let twh = bound[index - level] {
                return twh.fillHoles()?.adjust(level: 0, delta: level)
            } else {
                return tm
            }
        case let .free(v, params: params):
            guard let params = app(level: level, params) else { return nil }
            if let twh = free[v] {
                let adjusted = params.map { p in p.adjust(level: level, delta: -level) }
                return twh.fillHoles(adjusted)?.adjust(level: 0, delta: level)
            } else {
                return .free(v, params: params)
            }
        case let .const(c, binders: binders, params: params):
            guard let params = apply(level: level + binders.count, params) else { return nil }
            return .const(c, binders: binders, params: params)
        }
    }
    
    public static func varSubst(_ table : [Var : Var]) -> TmSubstitution {
        let free = table.mapValues { v in TmWithHoles(Tm.free(v, params: [])) }
        return TmSubstitution(free: free)
    }
    
    public static func reverseVarSubst(_ table : [Var : Var]) -> TmSubstitution {
        var reversedTable : [Var : Var] = [:]
        for (v, w) in table {
            reversedTable[w] = v
        }
        return varSubst(reversedTable)
    }
        
}
