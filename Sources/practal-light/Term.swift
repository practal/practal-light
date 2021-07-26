//
//  Term.swift
//  
//  Created by Steven Obua on 25/07/2021.
//

import Foundation

public typealias Var = Id
public typealias Const = Id

public enum Term : Hashable {
    case variable(Var, dependencies: [Var])
    case constant(Const, binders: [Var], params: [Term])
}

extension Term {

    public var isVariable : Bool {
        switch self {
        case .variable: return true
        case .constant: return false
        }
    }
    
    public var isConstant : Bool {
        switch self {
        case .variable: return false
        case .constant: return true
        }
    }
    
    public var `var` : Var? {
        switch self {
        case let .variable(v, dependencies: _): return v
        case .constant: return nil
        }
    }
    
    public var const : Const? {
        switch self {
        case let .constant(c, binders: _, params: _): return c
        case .variable: return nil
        }
    }

}

extension Term : CustomStringConvertible {
    
    public var description: String {
        switch self {
        case let .variable(v, dependencies: deps):
            if deps.isEmpty {
                return v.description
            } else {
                let names = deps.map { v in v.description }
                return "\(v)[\(names.joined(separator: ", "))]"
            }
        case let .constant(c, binders: binders, params: params):
            let prefix = ([c.description] + binders.map { v in v.description }).joined(separator: " ")
            let ps : [String] = params.map { p in
                let q = p.description
                if p.isConstant {
                    return "(\(q))"
                } else {
                    return q
                }
            }
            return ([prefix + "."] + ps).joined(separator: " ")
        }
    }

}



