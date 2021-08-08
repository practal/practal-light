//
//  Term.swift
//  
//  Created by Steven Obua on 25/07/2021.
//

import Foundation

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
    
    public var unappliedVar : Var? {
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

public extension Term {
    
    static func subsumes(sub : [Var : Int], sup : [Var : Int]) -> Bool {
        for (v, a) in sub {
            guard let b = sup[v], b == a else { return false }
        }
        return true
    }
    
    static func fresh(_ name : Id, for term : Term) -> Var {
        var maxPrimes = -1
        func vcheck(_ v : Var) {
            guard v.name == name else { return }
            maxPrimes = max(maxPrimes, v.primes)
        }
        func check(_ term : Term) {
            switch term {
            case let .constant(_, binders: binders, params: params):
                for b in binders { vcheck(b) }
                for p in params { check(p) }
            case let .variable(v, params: params):
                vcheck(v)
                for p in params { check(p) }
            }
        }
        return Var(name: name, primes: maxPrimes + 1)
    }
    
    static func allVarsOf(_ term : Term) -> [Id : Int] {
        var primes : [Id : Int] = [:]
        func add(_ v : Var) {
            primes[v.name] = max(v.primes, primes[v.name, default: 0])
        }
        func collect(_ term : Term) {
            switch term {
            case let .variable(v, params: params):
                add(v)
                for p in params { collect(p) }
            case let .constant(_, binders: binders, params: params):
                for v in binders { add(v) }
                for p in params { collect(p) }
            }
        }
        collect(term)
        return primes
    }
    
    static func replace(const : Const, with w : Var, in term : Term) -> Term {
        func repl(_ term : Term) -> Term {
            switch term {
            case let .variable(v, params: params):
                return .variable(v, params: params.map(repl))
            case let .constant(const, binders: [], params: params):
                return .variable(w, params: params.map { p in replace(const: const, with: w, in: p) })
            case let .constant(const, binders: binders, params: params):
                return .constant(const, binders: binders, params: params.map(repl))
            }
        }
        return repl(term)
    }
    
    func arityOf(const : Const) -> (binders: Int, params: Int)? {
        switch self {
        case let .constant(c, binders: binders, params: params):
            if c == const {
                return (binders: binders.count, params: params.count)
            } else {
                for p in params {
                    if let arity = p.arityOf(const: const) {
                        return arity
                    }
                }
                return nil
            }
        case let .variable(_, params: params):
            for p in params {
                if let arity = p.arityOf(const: const) {
                    return arity
                }
            }
            return nil
        }
    }
    
    func contains(const : Const) -> Bool {
        return arityOf(const: const) != nil
    }
    
    static func mk_binary(_ op : Const, _ left : Term, _ right : Term) -> Term {
        return .constant(op, binders: [], params: [left, right])
    }
    
    static func mk_unary(_ op : Const, _ arg : Term) -> Term {
        return .constant(op, binders: [], params: [arg])
    }
    
    static func mk_nullary(_ op : Const) -> Term {
        return .constant(op, binders: [], params: [])
    }
    
    static let c_true = mk_nullary(.c_true)

    static let c_Prop = mk_nullary(.c_Prop)
    
    static func mk_eq(_ left : Term, _ right : Term) -> Term {
        return mk_binary(Const.c_eq, left, right)
    }

    static func mk_and(_ left : Term, _ right : Term) -> Term {
        return mk_binary(Const.c_and, left, right)
    }
    
    static func mk_in(_ left : Term, _ right : Term) -> Term {
        return mk_binary(Const.c_in, left, right)
    }

    static func mk_ands(_ terms : [Term]) -> Term {
        switch terms.count {
        case 0: return c_true
        case 1: return terms.first!
        default:
            var ands = terms.first!
            for t in terms.dropFirst() {
                ands = Term.mk_and(ands, t)
            }
            return ands
        }
    }

    static func mk_imp(_ left : Term, _ right : Term) -> Term {
        return mk_binary(Const.c_imp, left, right)
    }
    
    static func mk_ex(_ x : Var, _ body : Term) -> Term {
        return .constant(Const.c_ex, binders: [x], params: [body])
    }
    
    static func mk_all(_ x : Var, _ body : Term) -> Term {
        return .constant(Const.c_all, binders: [x], params: [body])
    }

    static func mk_all<Vars:Collection>(_ vars : Vars, _ body : Term) -> Term where Vars.Element == Var {
        var t = body
        for x in vars.reversed() {
            t = mk_all(x, t)
        }
        return t
    }

    static func mk_in_Prop(_ t : Term) -> Term {
        return mk_binary(Const.c_in, t, c_Prop)
    }
    
    static func dest_in_Prop(_ t : Term) -> Term? {
        switch t {
        case .variable: return nil
        case .constant(Const.c_in, binders: [], params: let params):
            guard params.count == 2, params[1] == c_Prop else { return nil }
            return params[0]
        default: return nil
        }
    }

}
