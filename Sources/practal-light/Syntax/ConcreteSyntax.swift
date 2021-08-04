//
//  ConcreteSyntax.swift
//
//  Created by Steven Obua on 26/07/2021.
//

import Foundation

public struct ConcreteSyntax : CustomStringConvertible, Hashable {
    
    public enum Priority : Hashable {
        case Atomic
        case None
        case Level(Float)
        
        public static func from(_ priority : Float?, default : Priority) -> Priority {
            if let p = priority {
                return .Level(p)
            } else {
                return `default`
            }
        }
    }
    
    public enum Fragment : Hashable {
        case Var(Var, raised: Bool)  // the raised vars get the next higher priority class
        case Space
        case Text(String)
        case Keyword(String)
    }

    public let fragments : [Fragment]
    public let priority : Priority
    
    public init(fragments : [Fragment], priority : Priority = .None) {
        self.fragments = fragments
        self.priority = priority
    }
    
    public func withPriority(_ priority : Priority) -> ConcreteSyntax {
        return ConcreteSyntax(fragments: fragments, priority: priority)
    }
    
    public var description : String {
        let frags : [String] = fragments.map { f in
            switch f {
            case .Space: return "␣"
            case let .Var(v, raised: raised): if raised { return "\(v)" } else { return "`\(v)" }
            case .Text(let t): return "'\(t)'"
            case .Keyword(let t): return "@'\(t)'"
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
            case .Space, .Text, .Keyword: return f
            case let .Var(v, _): if select(v) { return f } else { return .Keyword(v.description) }
            }
        }
        return ConcreteSyntax(fragments: fs, priority: priority)
    }
    
    public var vars : [Var] {
        var vs : [Var] = []
        for f in fragments {
            switch f {
            case let .Var(v, _): vs.append(v)
            case .Space, .Text, .Keyword: break
            }
        }
        return vs
    }
    
    public var hasDuplicateVarOccurrences : Bool {
        let vs = vars
        return vs.count != Set(vs).count
    }
    

}

