//
//  AbstractSyntax.swift
//  
//
//  Created by Steven Obua on 04/08/2021.
//

import Foundation

public struct AbstractSyntax : Hashable {
    
    public let const : Const
    
    public let binders : [Var]
    
    public let params : [Term]
    
    public var term : Term {
        return .constant(const, binders: binders, params: params)
    }
    
    public var freeVars : [Var : Int] {
        var vs : [Var : Int] = [:]
        for p in params {
            switch p {
            case let .variable(v, deps): vs[v] = deps.count
            case .constant: fatalError("internal error")
            }
        }
        return vs
    }
    
    public var allVars : [Var : Int] {
        var vs = freeVars
        for v in binders {
            vs[v] = 0
        }
        return vs
    }
    
    public func binderOf(_ v : Var) -> Int? {
        return binders.firstIndex(of: v)
    }
    
    public func paramOf(_ v : Var) -> Int? {
        params.firstIndex { term in
            switch term {
            case let .variable(w, _) where v == w: return true
            default: return false
            }
        }
    }
    
    public func selectBoundVars(param : Int, binders _binders : [Var]) -> [Var] {
        var vars : [Var] = []
        switch params[param] {
        case let .variable(_, params: params):
            for p in params {
                guard let d = p.boundVar else {
                    fatalError()
                }
                let i = binderOf(d)!
                vars.append(_binders[i])
            }
        case .constant: fatalError()
        }
        return vars
    }
    
}

public struct ConstSyntax {
    
    public let abstractSyntax : AbstractSyntax
    
    public var concreteSyntaxes : [ConcreteSyntax]

    public mutating func append(_ concreteSyntax : ConcreteSyntax) {
        concreteSyntaxes.append(concreteSyntax)
    }
}
