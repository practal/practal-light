//
//  ConcreteSyntax.swift
//
//  Created by Steven Obua on 26/07/2021.
//

import Foundation

public typealias Syntax = [(SyntaxPattern, [ConcreteSyntax])]

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
    
    public static let CONTROL_PRIO : Float = 0
    public static let BINDER_PRIO : Float = 10
    public static let LOGIC_PRIO : Float = 20
    public static let REL_PRIO : Float = 30
    public static let TYPE_PRIO : Float = 40
    //public static let ARITH_PRIO : Float = 50
    public static let APP_PRIO : Float = 60
    
    public static let IMP_RPRIO : Float = 0.1
    public static let OR_RPRIO : Float = 0.2
    public static let AND_RPRIO : Float = 0.3
    public static let NOT_RPRIO : Float = 0.4
    
    public static let UNION_RPRIO : Float = 0.1
    public static let FUN_RPRIO : Float = 0.2
    public static let BINARY_UNION_RPRIO : Float = 0.3
    public static let BINARY_INTERSECTION_RPRIO : Float = 0.4
    public static let TYPE_RPRIO : Float = 0.5
    
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

