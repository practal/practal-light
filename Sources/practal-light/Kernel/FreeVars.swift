//
//  FreeVars.swift
//  
//
//  Created by Steven Obua on 10/08/2021.
//

import Foundation

public struct FreeVars {
    
    private var _arities : [Var : Int]
    
    public var arities : [Var : Int] { return _arities }

    public init(_ arities : [Var : Int] = [:]) {
        self._arities = arities
    }
    
    public init(_ tm : Tm) {
        _arities = [:]
        self.add(tm)
    }
    
    public var vars : Set<Var> {
        return Set(_arities.keys)
    }
    
    @discardableResult
    public mutating func add(_ v : Var, arity : Int) -> Bool {
        if let a = _arities[v] {
            return a == arity
        } else {
            _arities[v] = arity
            return true
        }
    }
        
    @discardableResult
    public mutating func add(_ tm : Tm) -> Bool {
        func collect(_ tm : Tm) -> Bool {
            switch tm {
            case .bound: return true
            case let .free(v, params: params):
                if let a = _arities[v] {
                    guard a == params.count else {
                        return false
                    }
                } else {
                    _arities[v] = params.count
                }
                for p in params {
                    guard collect(p) else { return false }
                }
                return true
            case let .const(_, binders: _, params: params):
                for p in params {
                    guard collect(p) else { return false }
                }
                return true
            }
        }
        return collect(tm)
    }
    
    public subscript(_ v : Var) -> Int? {
        return _arities[v]
    }
    
    public func contains(_ v : Var) -> Bool {
        return _arities[v] != nil
    }
    
    @discardableResult
    public mutating func add(_ freeVars : FreeVars) -> Bool {
        for (v, a) in freeVars.arities {
            if let b = _arities[v] {
                guard a == b else { return false }
            } else {
                _arities[v] = a
            }
        }
        return true
    }
    
    public func fresh(_ v : Var) -> Var {
        var v = v
        while contains(v) {
            v = v.increment()
        }
        return v
    }
    
    public mutating func addFresh(_ v : Var, arity : Int) -> Var {
        let v = fresh(v)
        _arities[v] = arity
        return v
    }
        
    public mutating func addFresh(_ tm : Tm, renaming : inout TmVarRenaming) -> Tm? {
        switch tm {
        case .bound: return tm
        case let .free(v, params: params):
            let freshParams = params.compactMap { p in addFresh(p, renaming: &renaming) }
            guard freshParams.count == params.count else { return nil }
            if let w = renaming[v] {
                guard self[w] == params.count else { return nil }
                return .free(w, params: freshParams)
            } else {
                let w = addFresh(v, arity: params.count)
                renaming[v] = w
                return .free(w, params: freshParams)
            }
        case let .const(c, binders: binders, params: params):
            let freshParams = params.compactMap { p in addFresh(p, renaming: &renaming) }
            guard freshParams.count == params.count else { return nil }
            return .const(c, binders: binders, params: freshParams)
        }
    }
    
    public mutating func addFresh(_ tm : Tm) -> (fresh: Tm, renaming: TmVarRenaming)? {
        var renaming = TmVarRenaming()
        guard let fresh = addFresh(tm, renaming: &renaming) else {
            return nil
        }
        return (fresh: fresh, renaming: renaming)
    }

    public mutating func addFresh(_ tms : [Tm]) -> (freshs: [Tm], renaming: TmVarRenaming)? {
        var renaming = TmVarRenaming()
        var freshs : [Tm] = []
        for tm in tms {
            guard let fresh = addFresh(tm, renaming: &renaming) else {
                return nil
            }
            freshs.append(fresh)
        }
        return (freshs: freshs, renaming: renaming)
    }

}
