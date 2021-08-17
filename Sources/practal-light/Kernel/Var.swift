//
//  Var.swift
//  
//
//  Created by Steven Obua on 05/08/2021.
//

import Foundation

public struct Var : Hashable, CustomStringConvertible, Comparable {
    
    public static let PRIME : Character = "’"
    
    public let name : Id
    public let primes : Int
    
    public init(name : Id, primes : Int = 0) {
        guard primes >= 0 else { fatalError() }
        self.name = name
        self.primes = primes
    }
    
    public init?(_ primed: String) {
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
    
    public func increment() -> Var {
        return Var(name: name, primes: primes + 1)
    }
    
    public static func < (lhs: Var, rhs: Var) -> Bool {
        return lhs.name.id < rhs.name.id || (lhs.name.id == rhs.name.id && lhs.primes < rhs.primes)
    }
    
}
