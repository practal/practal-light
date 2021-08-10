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
    public mutating func addAtomic(_ tm : Tm) -> Bool {
        var newArities = _arities
        func collect(_ tm : Tm) -> Bool {
            switch tm {
            case .bound: return true
            case let .free(v, params: params):
                if let a = newArities[v] {
                    guard a == params.count else {
                        return false
                    }
                } else {
                    newArities[v] = params.count
                }
                return true
            case let .const(_, binders: _, params: params):
                for p in params {
                    guard addAtomic(p) else { return false }
                }
                return true
            }
        }
        guard collect(tm) else { return false }
        _arities = newArities
        return true
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
                return true
            case let .const(_, binders: _, params: params):
                for p in params {
                    guard addAtomic(p) else { return false }
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
    public mutating func addAtomic(_ freeVars : FreeVars) -> Bool {
        var newArities = _arities
        for (v, a) in freeVars.arities {
            if let b = newArities[v] {
                guard a == b else { return false }
            } else {
                newArities[v] = a
            }
        }
        _arities = newArities
        return true
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
    
    public mutating func addFresh(_ tm : Tm) -> (fresh: Tm, renaming: TmVarRenaming)? {
        
        var renaming = TmVarRenaming()
                
        func rename(_ v : Var, arity : Int) -> Var? {
            if let w = renaming[v] {
                guard self[w] == arity else { return nil }
                return w
            } else {
                let w = addFresh(v, arity: arity)
                renaming[v] = w
                return w
            }
        }
        
        func make(_ tm : Tm) -> Tm? {
            switch tm {
            case .bound: return tm
            case let .free(v, params: params):
                let freshParams = params.compactMap(make)
                guard freshParams.count == params.count else { return nil }
                guard let w = rename(v, arity: params.count) else { return nil }
                return .free(w, params: freshParams)
            case let .const(c, binders: binders, params: params):
                let freshParams = params.compactMap(make)
                guard freshParams.count == params.count else { return nil }
                return .const(c, binders: binders, params: freshParams)
            }
        }
        
        guard let freshTm = make(tm) else { return nil }
        
        return (fresh: freshTm, renaming: renaming)
    }
    
}
