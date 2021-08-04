//
//  Term.swift
//  
//  Created by Steven Obua on 25/07/2021.
//

import Foundation

public struct Var : Hashable, CustomStringConvertible {
    
    public static let PRIME : Character = "’"
    
    public let name : Id
    public let primes : Int
    
    public init(name : Id, primes : Int = 0) {
        guard primes >= 0 else { fatalError() }
        self.name = name
        self.primes = primes
    }
    
    public init?(primed: String) {
        var t = primed
        var primes = 0
        while t.last == Var.PRIME {
            t.removeLast()
            primes += 1
        }
        guard let id = Id(t) else { return nil }
        self.name = id
        self.primes = primes
    }
    
    public var description : String {
        var d = name.description
        for _ in 0 ..< primes {
            d.append(Var.PRIME)
        }
        return d
    }
    
}

public struct Namespace : Hashable {
    
    public static let SEPARATOR : Character = "."
    
    public var components : [Id]
    
    public init(_ components : [Id] = []) {
        self.components = components
    }
    
    public var isEmpty : Bool {
        return components.isEmpty
    }
}

public struct Const : Hashable, CustomStringConvertible {
    public let namespace : Namespace
    public let name : Id
    
    public init(namespace : Namespace = Namespace(), name : Id) {
        self.namespace = namespace
        self.name = name
    }
    
    public init?(qualified : String) {
        let splits = qualified.split(separator: Namespace.SEPARATOR, omittingEmptySubsequences: false)
        if splits.isEmpty { return nil }
        var ids : [Id] = []
        for s in splits {
            guard let id = Id(String(s)) else { return nil }
            ids.append(id)
        }
        self.name = ids.removeLast()
        self.namespace = Namespace(ids)
    }
    
    public var description: String {
        var d = name.description
        for n in namespace.components.reversed() {
            d = "\(n)\(Namespace.SEPARATOR)\(d)"
        }
        return d
    }
}

public enum Term : Hashable {
    case variable(Var, params: [Term])
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
        case let .variable(v, params: _): return v
        case .constant: return nil
        }
    }
    
    public var `boundVar` : Var? {
        switch self {
        case let .variable(v, params: []): return v
        default: return nil
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
        case let .variable(v, params: params):
            if params.isEmpty {
                return v.description
            } else {
                let ps = params.map { p in p.description }
                return "\(v)[\(ps.joined(separator: ", "))]"
            }
        case let .constant(c, binders: binders, params: params):
            let prefix = ([c.description] + binders.map { v in v.description }).joined(separator: " ")
            let ps : [String] = params.map { p in p.description }
            return "(" + ([prefix + "."] + ps).joined(separator: " ") + ")"
        }
    }

}




