//
//  Substitution.swift
//  
//
//  Created by Steven Obua on 08/08/2021.
//

import Foundation

public struct TermWithHoles {
    
    public let holes : [Var]
    
    public let term : Term
    
    public init(_ holes : [Var], _ term : Term) {
        self.holes = holes
        self.term = term
    }

}

public typealias Substitution = [Var : TermWithHoles]

internal enum FVTerm {
    
    case variable(Var, params: [FVTerm], freeVars: Set<Var>)
    
    case constant(Const, binders: [Var], params: [FVTerm], freeVars: Set<Var>)
    
    public var freeVars : Set<Var> {
        switch self {
        case let .variable(_, params: _, freeVars: freeVars): return freeVars
        case let .constant(_, binders: _, params: _, freeVars: freeVars): return freeVars
        }
    }
    
    public var term : Term {
        switch self {
        case let .variable(v, params: fvparams, freeVars: _):
            return .variable(v, params: fvparams.map { p in p.term })
        case let .constant(c, binders: binders, params: fvparams, freeVars: _):
            return .constant(c, binders: binders, params: fvparams.map { p in p.term })
        }
    }
    
    public static func freeVarsOf(_ terms : [FVTerm]) -> Set<Var> {
        var fs : Set<Var> = []
        for t in terms {
            fs.formUnion(t.freeVars)
        }
        return fs
    }
    
    public func collectAllVars(_ vars : inout Set<Var>) {
        switch self {
        case let .variable(v, params: params, freeVars: _):
            vars.insert(v)
            for p in params {
                p.collectAllVars(&vars)
            }
        case let .constant(_, binders: binders, params: params, freeVars: _):
            vars.formUnion(binders)
            for p in params {
                p.collectAllVars(&vars)
            }
        }
    }

    
}

internal struct FVTermWithHoles {
    
    public let holes : [Var]
    
    public let term : FVTerm
    
    public let freeVars : Set<Var>
    
    public init(_ holes : [Var], _ term : FVTerm) {
        self.holes = holes
        self.term = term
        self.freeVars = term.freeVars.subtracting(holes)
    }

}

internal typealias FVSubstitution = [Var : FVTermWithHoles]

extension KernelContext {
    
    internal func FVTermOf(_ term : Term) -> FVTerm {
        switch term {
        case let .variable(v, params: params):
            let fparams = params.map(FVTermOf)
            return .variable(v, params: fparams, freeVars: FVTerm.freeVarsOf(fparams).union([v]))
        case let .constant(c, binders: binders, params: params):
            let fparams = params.map(FVTermOf)
            return mkConstant(const: c, binders: binders, params: fparams)
        }
    }
    
    internal func mkConstant(const : Const, binders : [Var], params : [FVTerm]) -> FVTerm {
        guard let head = constants[const]?.head,
              head.binders.count == binders.count, head.params.count == params.count // cheap sanity checks
        else { fatalError() }
        var frees : Set<Var> = []
        for (i, p) in params.enumerated() {
            let boundVars = head.selectBoundVars(param: i, binders: binders)
            frees.formUnion(p.freeVars.subtracting(boundVars))
        }
        return .constant(const, binders: binders, params: params, freeVars: frees)
    }

    private func rename(_ renaming : [Var : Var], in term : FVTerm) -> FVTerm {
        
        func r(boundVars : Set<Var>, _ term : FVTerm) -> FVTerm {
            switch term {
            case let .variable(v, params: params, freeVars: _) where boundVars.contains(v):
                guard params.isEmpty else { fatalError() }
                return term
            case let .variable(v, params: params, freeVars: _):
                let rparams = params.map { p in r(boundVars: boundVars, p) }
                let v = renaming[v, default: v]
                return .variable(v, params: rparams, freeVars: FVTerm.freeVarsOf(rparams).union([v]))
            case let .constant(const, binders: binders, params: params, freeVars: _):
                let head = constants[const]!.head
                var rparams : [FVTerm] = []
                for (i, p) in params.enumerated() {
                    let boundVars = boundVars.union(head.selectBoundVars(param: i, binders: binders))
                    rparams.append(r(boundVars: boundVars, p))
                }
                return mkConstant(const: const, binders: binders, params: rparams)
            }

        }
        
        return r(boundVars : [], term)
    }
        
    internal func substitute(_ substitution : FVSubstitution, in term : FVTerm) -> FVTerm? {
                
        if substitution.isEmpty || term.freeVars.isEmpty { return term }
        
        let varsToBeSubstituted = Set(substitution.keys)

        func substMultiple(boundVars : Set<Var>, terms : [FVTerm]) -> [FVTerm]? {
            var result : [FVTerm] = []
            for t in terms {
                guard let s = subst(boundVars: boundVars, term: t) else { return nil }
                result.append(s)
            }
            return result
        }
        
        func renameAndSubst(boundVars : Set<Var>, const : Const, binders : [Var], params : [FVTerm],
                            clashingBoundVars : Set<Var>) -> FVTerm?
        {
            var allVars : Set<Var> = boundVars // Including boundVars is not necessary, but nicer.
            allVars.formUnion(binders)
            for p in params {
                p.collectAllVars(&allVars)
            }
            var renaming : [Var : Var] = [:]
            for b in binders {
                guard clashingBoundVars.contains(b) else {
                    continue
                }
                var nb = b.increment()
                while allVars.contains(nb) {
                    nb = nb.increment()
                }
                renaming[b] = nb
                allVars.insert(nb)
            }
            let rbinders = binders.map { v in renaming[v, default: v] }
            let rparams = params.map { p in rename(renaming, in: p) }
            let term = mkConstant(const: const, binders: rbinders, params: rparams)
            return subst(boundVars: boundVars, term: term)
        }
        
        func subst(boundVars : Set<Var>, term : FVTerm) -> FVTerm? {
            guard !varsToBeSubstituted.isDisjoint(with: term.freeVars) else { return term }
            switch term {
            case let .variable(v, params: params, freeVars: _):
                guard !boundVars.contains(v) else { return term }
                guard let params = substMultiple(boundVars: boundVars, terms: params) else { return nil }
                if let termWithHoles = substitution[v] {
                    guard termWithHoles.holes.count == params.count else { return nil }
                    var subst = FVSubstitution()
                    for (i, hole) in termWithHoles.holes.enumerated() {
                        subst[hole] = FVTermWithHoles([], params[i])
                    }
                    return substitute(subst, in: termWithHoles.term)
                } else {
                    return .variable(v, params: params, freeVars: FVTerm.freeVarsOf(params))
                }
            case let .constant(c, binders: binders, params: params, freeVars: _):
                guard let head = constants[c]?.head else { return nil }
                var clashingBoundVars : Set<Var> = []
                for (i, param) in params.enumerated() {
                    let boundVars = head.selectBoundVars(param: i, binders: binders)
                    // Does the param have any free variables such that
                    // the terms to be substituted for these have free variables in boundVars?
                    // If so, we need to rename those boundVars.
                    for v in param.freeVars {
                        if let twh = substitution[v] {
                            clashingBoundVars.formUnion(twh.freeVars.intersection(boundVars))
                        }
                    }
                }
                guard clashingBoundVars.isEmpty else {
                    return renameAndSubst(boundVars: boundVars, const: c, binders: binders, params: params, clashingBoundVars: clashingBoundVars)
                }
                var sparams : [FVTerm] = []
                for (i, param) in params.enumerated() {
                    let boundVars = boundVars.union(head.selectBoundVars(param: i, binders: binders))
                    guard let sparam = subst(boundVars: boundVars, term: param) else { return nil }
                    sparams.append(sparam)
                }
                return mkConstant(const: c, binders: binders, params: sparams)
            }
        }
        
        return subst(boundVars: [], term: term)
    }
        
    internal func wellformedFVTermOf(_ term : Term) -> FVTerm? {
        guard isWellformed(term) else { return nil }
        return FVTermOf(term)
    }
    
    public func isWellformed(_ termWithHoles : TermWithHoles) -> Bool {
        guard let frees = checkWellformedness(termWithHoles.term) else { return false }
        for hole in termWithHoles.holes {
            guard let arity = frees.arity[hole] else { continue }
            guard arity == 0 else { return false }
        }
        return true
    }
    
    internal func FVTermWithHolesOf(_ termWithHoles : TermWithHoles) -> FVTermWithHoles {
        return FVTermWithHoles(termWithHoles.holes, FVTermOf(termWithHoles.term))
    }
    
    internal func wellformedFVSubstitutionOf(_ subst : Substitution) -> FVSubstitution? {
        var fvsubst : [Var : FVTermWithHoles] = [:]
        for (v, t) in subst {
            guard isWellformed(t) else { return nil }
            fvsubst[v] = FVTermWithHolesOf(t)
        }
        return fvsubst
    }
            
}


