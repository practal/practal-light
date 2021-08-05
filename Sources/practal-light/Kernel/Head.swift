//
//  Head.swift
//  
//
//  Created by Steven Obua on 05/08/2021.
//

import Foundation

public struct Head : Hashable {
    
    public let const : Const
    
    public let binders : [Var]
    
    public let params : [Term]
    
    public init?(const : Const, binders : [Var], params : [Term]) {
        let boundVars = Set(binders)
        guard boundVars.count == binders.count else { return nil }
        var paramsVars : Set<Var> = []
        for p in params {
            switch p {
            case .constant: return nil
            case let .variable(v, params: deps):
                guard !boundVars.contains(v) else { return nil }
                guard paramsVars.insert(v).inserted else { return nil }
                guard Set(deps).count == deps.count else { return nil }
                for d in deps {
                    guard let w = d.unappliedVar else { return nil }
                    guard boundVars.contains(w) else { return nil }
                }
            }
        }
        self.const = const
        self.binders = binders
        self.params = params
    }
    
    public var term : Term {
        return .constant(const, binders: binders, params: params)
    }
    
    public var freeVars : [Var : Int] {
        var vs : [Var : Int] = [:]
        for p in params {
            switch p {
            case let .variable(v, deps): vs[v] = deps.count
            case .constant: fatalError()
            }
        }
        return vs
    }
    
    public func covers(_ frees : [Var : Int]) -> Bool {
        return Term.subsumes(sub: frees, sup: freeVars)
    }
    
    public var allVars : [Var : Int] {
        var vs = freeVars
        for v in binders {
            vs[v] = 0
        }
        return vs
    }
    
    public func binderIndex(_ v : Var) -> Int? {
        return binders.firstIndex(of: v)
    }
    
    public func paramIndex(_ v : Var) -> Int? {
        params.firstIndex { term in
            switch term {
            case let .variable(w, _) where v == w: return true
            default: return false
            }
        }
    }
    
    public func selectBoundVars(param : Int, binders : [Var]) -> [Var] {
        var vars : [Var] = []
        switch params[param] {
        case let .variable(_, params: params):
            for p in params {
                guard let d = p.unappliedVar else {
                    fatalError()
                }
                let i = binderIndex(d)!
                vars.append(binders[i])
            }
        case .constant: fatalError()
        }
        return vars
    }
    
}
