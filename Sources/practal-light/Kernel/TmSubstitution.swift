//
//  TmSubstitution.swift
//  
//
//  Created by Steven Obua on 09/08/2021.
//

import Foundation

public struct TmWithHoles {
    
    public let holes : Int
    
    public let tm : Tm
    
    public init(holes : Int = 0, _ tm : Tm) {
        self.holes = holes
        self.tm = tm
    }
    
    public func fillHoles() -> Tm? {
        guard holes == 0 else { return nil }
        return tm
    }
    
    public func fillHoles(_ params : [Tm]) -> Tm? {
        guard params.count == holes else { return nil }
        var subst = TmSubstitution()
        let I = params.count - 1
        for (i, p) in params.enumerated() {
            subst[I - i] = TmWithHoles(p)
        }
        return subst.apply(level: params.count, tm)
    }

}

public struct TmSubstitution {
    
    private var free : [Var : TmWithHoles]
    private var bound : [Int : TmWithHoles]
    
    public init(free : [Var : TmWithHoles] = [:], bound : [Int : TmWithHoles] = [:]) {
        self.free = free
        self.bound = bound
    }
    
    public subscript(_ index : Int) -> TmWithHoles? {
        get {
            return bound[index]
        }
        
        set {
            bound[index] = newValue
        }
    }
            
    public var isEmpty : Bool {
        return free.isEmpty && bound.isEmpty
    }
    
    public func apply(level : Int = 0, _ tms : [Tm]) -> [Tm]? {
        guard !isEmpty else { return tms }
        return app(level: level, tms)
    }
    
    public func apply(level : Int, _ tm : Tm) -> Tm? {
        guard !isEmpty else { return tm }
        return app(level: level, tm)
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
                return twh.fillHoles()
            } else {
                return tm
            }
        case let .free(v, params: params):
            guard let params = app(level: level, params) else { return nil }
            if let twh = free[v] {
                return twh.fillHoles(params)
            } else {
                return .free(v, params: params)
            }
        case let .const(c, binders: binders, params: params):
            guard let params = apply(level: level + binders.count, params) else { return nil }
            return .const(c, binders: binders, params: params)
        }
    }
    
}
