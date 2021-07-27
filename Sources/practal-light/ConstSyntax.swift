//
//  ConstSyntax.swift
//
//  Created by Steven Obua on 26/07/2021.
//

import Foundation

public struct ConcreteSyntax : CustomStringConvertible, Hashable {
    
    public enum Fragment : Hashable {
        case Var(Var)
        case Space
        case Text(String)
    }

    public let fragments : [Fragment]
    
    public init(fragments : [Fragment]) {
        self.fragments = fragments
    }
    
    public var description : String {
        let frags : [String] = fragments.map { f in
            switch f {
            case .Space: return "␣"
            case .Var(let v): return v.description
            case .Text(let t): return "`\(t)`"
            }
        }
        return frags.joined()
    }
    
    public var normalized : ConcreteSyntax {
        var fs : [Fragment] = []
        var discard_space = true
        var text : String? = nil
        
        func closeText() {
            if text != nil {
                fs.append(.Text(text!))
                text = nil
            }
        }
        
        for f in fragments {
            switch f {
            case .Space where !discard_space:
                closeText()
                fs.append(.Space)
                discard_space = true
            case .Space where discard_space:
                break
            case .Text(let t) where text != nil:
                discard_space = false
                text!.append(t)
            case .Text(let t) where text == nil:
                discard_space = false
                text = t
            case .Var:
                closeText()
                fs.append(f)
            default: fatalError("internal error")
            }
        }
        
        closeText()
        
        while fs.last == .Space {
            fs.removeLast()
        }
        
        return ConcreteSyntax(fragments: fs)
    }
    
    public func selectVars(_ select : (Var) -> Bool) -> ConcreteSyntax {
        let fs : [Fragment] = fragments.map { f in
            switch f {
            case .Space, .Text: return f
            case .Var(let v): if select(v) { return f } else { return .Text(v.description) }
            }
        }
        return ConcreteSyntax(fragments: fs)
    }
    
    public var vars : [Var] {
        var vs : [Var] = []
        for f in fragments {
            switch f {
            case let .Var(v): vs.append(v)
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
    
}

public struct ConstSyntax {
    
    public let abstractSyntax : AbstractSyntax
    
    public var concreteSyntaxes : [ConcreteSyntax]

    public mutating func append(_ concreteSyntax : ConcreteSyntax) {
        concreteSyntaxes.append(concreteSyntax)
    }
}
