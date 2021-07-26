//
//  Term.swift
//  
//  Created by Steven Obua on 25/07/2021.
//

import Foundation

public typealias Var = String
public typealias Const = String

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



