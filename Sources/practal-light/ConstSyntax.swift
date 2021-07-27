//
//  ConstSyntax.swift
//
//  Created by Steven Obua on 26/07/2021.
//

import Foundation

public struct ConcreteSyntax : CustomStringConvertible, Hashable {
    
    public enum Fragment : Hashable {
        case Var(Var, raised: Bool)  // the raised vars get the next higher priority class
        case Space
        case Text(String)
    }

    public let fragments : [Fragment]
    public let priority : Float?
    
    public init(fragments : [Fragment], priority : Float?) {
        self.fragments = fragments
        self.priority = priority
    }
    
    public func withPriority(_ priority : Float?) -> ConcreteSyntax {
        return ConcreteSyntax(fragments: fragments, priority: priority)
    }
    
    public var description : String {
        let frags : [String] = fragments.map { f in
            switch f {
            case .Space: return "␣"
            case let .Var(v, raised: raised): if raised { return "^\(v)" } else { return "\(v)" }
            case .Text(let t): return "`\(t)`"
            }
        }
        return frags.joined()
    }
    
    public var normalized : ConcreteSyntax {
                
        func simp(_ a : Fragment, _ b : Fragment) -> Fragment? {
            switch (a, b) {
            case let (.Text(u), .Text(v)): return .Text(u + v)
            case (.Space, .Space): return .Space
            default: return nil
            }
        }
        
        guard var current = fragments.first else { return self }
        var result : [Fragment] = []
        for f in fragments.dropFirst() {
            if let s = simp(current, f) {
                current = s
            } else {
                result.append(current)
                current = f
            }
        }
        result.append(current)
        
        if result.first == .Space {
            result.removeFirst()
        }
        
        if result.last == .Space {
            result.removeLast()
        }

        return ConcreteSyntax(fragments: result, priority: priority)
    }
    
    public func selectVars(_ select : (Var) -> Bool) -> ConcreteSyntax {
        let fs : [Fragment] = fragments.map { f in
            switch f {
            case .Space, .Text: return f
            case let .Var(v, _): if select(v) { return f } else { return .Text(v.description) }
            }
        }
        return ConcreteSyntax(fragments: fs, priority: priority)
    }
    
    public var vars : [Var] {
        var vs : [Var] = []
        for f in fragments {
            switch f {
            case let .Var(v, _): vs.append(v)
            case .Space, .Text: break
            }
        }
        return vs
    }
    
    public var hasDuplicateVarOccurrences : Bool {
        let vs = vars
        return vs.count != Set(vs).count
    }
    

}

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
        case let .variable(_, dependencies: deps):
            for d in deps {
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
