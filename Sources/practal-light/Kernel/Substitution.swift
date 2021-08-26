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

public struct TmWithHoles : CustomStringConvertible {
    
    public let holes : Int
    
    public let tm : Tm
    
    public init(holes : Int, _ tm : Tm) {
        self.holes = holes
        self.tm = tm
    }
    
    public init?(_ kc : KernelContext, wellformed termWithHoles : TermWithHoles) {
        guard let tm = Tm.fromWellformedTerm(kc, term: termWithHoles.term) else { return nil }
        var subst = TmSubstitution()
        holes = termWithHoles.holes.count
        for (i, v) in termWithHoles.holes.enumerated() {
            subst[v] = TmWithHoles(holes: 0, .bound(i))
        }
        if let tm = subst.apply(tm) {
            self.tm = tm
        } else {
            return nil
        }
    }
    
    public var size : Int {
        return tm.size
    }
    
    public func incrementDangling(delta : Int) -> TmWithHoles {
        guard delta >= 0 else { fatalError() }
        let atm = tm.incrementDangling(level: holes, delta: delta)
        return TmWithHoles(holes: holes, atm)
    }
    
    public func fillHoles() -> Tm? {
        guard holes == 0 else { return nil }
        return tm
    }
    
    public func fillHoles(_ params : [Tm]) -> Tm? {
        guard params.count == holes else { return nil }
        var subst = TmSubstitution()
        for (i, p) in params.enumerated() {
            subst[i] = TmWithHoles(holes: 0, p)
        }
        return subst.apply(level: 0, tm)
    }
    
    public var description : String {
        return "([\(holes)] \(tm))"
    }

}

public struct TmVarRenaming {
    
    private var table : [Var : Var]
    
    public init(_ table : [Var : Var] = [:]) {
        self.table = table
    }
    
    public func apply(_ tm : Tm) -> Tm {
        switch tm {
        case .bound: return tm
        case let .free(v, params: params):
            let w = table[v, default: v]
            return .free(w, params: params.map(apply))
        case let .const(c, binders: binders, params: params):
            return .const(c, binders: binders, params: params.map(apply))
        }
    }
    
    public func apply(_ twh : TmWithHoles) -> TmWithHoles {
        return TmWithHoles(holes: twh.holes, apply(twh.tm))
    }

    public func reversed() -> TmVarRenaming {
        var rtable : [Var : Var] = [:]
        for (v, w) in table {
            rtable[w] = v
        }
        return TmVarRenaming(rtable)
    }
    
    public subscript(_ v : Var) -> Var? {
        get {
            return table[v]
        }
        set {
            table[v] = newValue
        }
    }
    
    public var codomain : Set<Var> {
        return Set(table.values)
    }
    
    public var domain : Set<Var> {
        return Set(table.keys)
    }
        
}

public struct TmSubstitution : CustomStringConvertible {
    
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
    
    public var description : String {
        var mappings : [(String, String)] = []
        for (v, t) in (free.sorted { e1, e2 in e1.key < e2.key }) {
            mappings.append((v.description, t.description))
        }
        for (i, t) in (bound.sorted { e1, e2 in e1.key < e2.key }) {
            mappings.append((i.description, t.description))
        }
        return "[\(mappings.map { m in "\(m.0) → \(m.1)"} .joined(separator: ", "))]"
    }
    
    public var size : Int {
        var s = 0
        for (_, t) in free {
            s += t.size
        }
        for (_, t) in bound {
            s += t.size
        }
        return s
    }
    
    public mutating func restrict(_ vars : Set<Var>) {
        free = free.filter { (v, _) in vars.contains(v) }
    }
        
    public var freeMappings : [Var : TmWithHoles] { return free }
    
    public var boundMappings : [Int : TmWithHoles] { return bound }
        
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
            guard let s = subst.apply(t) else {
                print("could not substitute in \(t)")
                return false
            }
            newFree[v] = s
        }
        for (i, t) in bound {
            guard let s = subst.apply(t) else {
                print("could not substitute in \(t)")
                return false
            }
            newBound[i] = s
        }
        for (v, t) in subst.free {
            if newFree[v] == nil {
                newFree[v] = t
            }
        }
        for (i, t) in subst.bound {
            if newBound[i] == nil {
                newBound[i] = t
            }
        }
        free = newFree
        bound = newBound
        return true
    }
    
    public mutating func compose(_ renaming : TmVarRenaming) {
        free = free.mapValues { t in renaming.apply(t) }
        bound = bound.mapValues { t in renaming.apply(t) }
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
                let twh = twh.incrementDangling(delta: level)
                return twh.fillHoles()
            } else {
                return tm
            }
        case let .free(v, params: params):
            guard let params = app(level: level, params) else { return nil }
            if let twh = free[v] {
                let twh = twh.incrementDangling(delta: level)
                return twh.fillHoles(params)
            } else {
                return .free(v, params: params)
            }
        case let .const(c, binders: binders, params: params):
            guard let params = apply(level: level + binders.count, params) else { return nil }
            return .const(c, binders: binders, params: params)
        }
    }
    
    public static func varSubst(_ table : [Var : Var]) -> TmSubstitution {
        let free = table.mapValues { v in TmWithHoles(holes: 0, Tm.free(v, params: [])) }
        return TmSubstitution(free: free)
    }
    
    public static func reverseVarSubst(_ table : [Var : Var]) -> TmSubstitution {
        var reversedTable : [Var : Var] = [:]
        for (v, w) in table {
            reversedTable[w] = v
        }
        return varSubst(reversedTable)
    }
    
    public func isWellformed(_ kc : KernelContext, _ frees : inout FreeVars) -> Bool {
        guard bound.isEmpty else { return false }
        return free.values.allSatisfy { twh in kc.isWellformed(twh, &frees) }
    }
        
}

extension KernelContext {
    
    public func isWellformed(_ twh : TmWithHoles, _ frees : inout FreeVars) -> Bool {
        return isWellformed(level: twh.holes, twh.tm, &frees)
    }
    
    public func isWellformed(_ twh : TmWithHoles) -> Bool {
        var frees = FreeVars()
        return isWellformed(twh, &frees)
    }
    
    public func isWellformed(_ subst : TmSubstitution) -> Bool {
        var frees = FreeVars()
        return subst.isWellformed(self, &frees)
    }
}
