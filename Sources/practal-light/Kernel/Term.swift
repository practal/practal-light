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
    static let c_false = mk_nullary(.c_false)
    static let c_nil = mk_nullary(.c_nil)
    static let c_Prop = mk_nullary(.c_Prop)
    
    static func mk_eq(_ left : Term, _ right : Term) -> Term {
        return mk_binary(Const.c_eq, left, right)
    }

    static func mk_not(_ prop : Term) -> Term {
        return mk_unary(.c_not, prop)
    }
    
    static func mk_defined(_ term : Term) -> Term {
        return mk_unary(.c_defined, term)
    }

    static func mk_undefined(_ term : Term) -> Term {
        return mk_unary(.c_undefined, term)
    }

    static func mk_and(_ left : Term, _ right : Term) -> Term {
        return mk_binary(Const.c_and, left, right)
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

    static func mk_or(_ left : Term, _ right : Term) -> Term {
        return mk_binary(Const.c_or, left, right)
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

    static func mk_in_Prop(_ t : Term) -> Term {
        return mk_binary(Const.c_in, t, c_Prop)
    }

}




