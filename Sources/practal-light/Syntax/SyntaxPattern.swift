//
//  SyntaxPattern.swift
//  
//
//  Created by Steven Obua on 03/08/2021.
//

import Foundation

public enum SyntaxPattern : Hashable {
    case variable(Var)
    case constant(Const, binders: [Var], params: [SyntaxPattern])
    
    public var isPattern : Bool {
        switch self {
        case .variable: return false
        case .constant:
            var vars : Set<Var> = []
            return self.isPattern(&vars)
        }
    }
    
    private func isPattern(_ vars : inout Set<Var>) -> Bool {
        switch self {
        case .variable(let v):
            guard !vars.contains(v) else { return false }
            vars.insert(v)
            return true
        case let .constant(_, binders: binders, params: params):
            for v in binders {
                guard !vars.contains(v) else { return false }
                vars.insert(v)
                for p in params {
                    guard p.isPattern(&vars) else { return false }
                }
            }
            return true
        }
    }
    
    public func containsBinder(_ v : Var) -> Bool {
        switch self {
        case .variable: return false
        case let .constant(_, binders: binders, params: params):
            if binders.contains(v) { return true }
            for p in params {
                if p.containsBinder(v) { return true }
            }
            return false
        }
    }
    
    public func instantiate(_ sbinders : [Var : Var], _ sterms : [Var : Term]) -> Term {
        switch self {
        case let .variable(v):
            return sterms[v]!
        case let .constant(const, binders: binders, params: params):
            let iparams = params.map { p in p.instantiate(sbinders, sterms) }
            let ibinders = binders.map { v in sbinders[v]! }
            return .constant(const, binders: ibinders, params: iparams)
        }
    }
    
    public static func from(_ term : Term) -> SyntaxPattern {
        switch term {
        case let .variable(v, params: _): return .variable(v)
        case let .constant(const, binders: binders, params: params):
            return .constant(const, binders: binders, params: params.map(from))
        }
    }
}
