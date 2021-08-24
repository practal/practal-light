//
//  Unification.swift
//
//  Created by Steven Obua on 24/08/2021.
//

import Foundation

public struct Unification {
    
    public struct Constraint : CustomStringConvertible, Hashable {
        
        let level : Int
                
        let lhs : Tm
        
        let rhs : Tm
        
        init(level : Int, lhs : Tm, rhs : Tm) {
            self.level = level
            self.lhs = lhs
            self.rhs = rhs
        }
        
        func apply(_ subst : TmSubstitution) -> Constraint? {
            guard let l = subst.apply(level: level, lhs) else { return nil }
            guard let r = subst.apply(level: level, rhs) else { return nil }
            return Constraint(level: level, lhs: l, rhs: r)
        }
        
        public var description: String {
            return "[\(level)] \(lhs) ≟ \(rhs)"
        }
        
        public var size: Int {
            return max(lhs.size, rhs.size)
        }
        
        var reversed: Constraint {
            return Constraint(level: level, lhs: rhs, rhs: lhs)
        }
                
        var isTrivial : Bool {
            return lhs == rhs
        }
        
    }
    
    public struct Action {
        let addConstraints : [Constraint]
        let addElimVars : [Var]
        let addIdVars : [Var]
        let branches : [TmSubstitution]?
        
        static let fail = Action(branches: [])
        static let succeed = Action()
        
        init(addConstraints: [Constraint] = [], addElimVars: [Var] = [], addIdVars: [Var] = [], branches: [TmSubstitution]? = nil) {
            self.addConstraints = addConstraints
            self.addElimVars = addElimVars
            self.addIdVars = addIdVars
            self.branches = branches
        }
        
        static func branch(_ constraints : [Constraint], _ v : Var, _ twhs : [TmWithHoles]) -> Action {
            let substs = twhs.map { t in TmSubstitution(free : [v : t]) }
            return Action(addConstraints: constraints, branches: substs)
        }
    }
    
    public typealias Fresh = (Var, Int) -> Var
    
    public typealias Strategy = (UnificationParams, Constraint) -> Action?
    
    public struct Leaf : CustomStringConvertible {
        
        private let substitution : TmSubstitution
        
        private let constraints : [Constraint]
        
        private let elimVars : Set<Var>
        
        private let idVars : Set<Var>
        
        
        init(constraints : [Constraint]) {
            self.substitution = TmSubstitution()
            self.constraints = constraints
            self.elimVars = []
            self.idVars = []
        }
        
        private init(_ substitution : TmSubstitution, _ constraints : [Constraint], _ elimVars : Set<Var>, _ idVars : Set<Var>) {
            self.substitution = substitution
            self.constraints = constraints
            self.elimVars = elimVars
            self.idVars = idVars
        }
        
        var size : Int {
            return substitution.size
        }
                        
        func substitute(_ subst : TmSubstitution) -> Leaf? {
            let newConstraints = constraints.compactMap { c in c.apply(subst) }
            guard newConstraints.count == constraints.count else { return nil }
            var s = substitution
            guard s.compose(subst) else { return nil }
            return Leaf(s, newConstraints, elimVars, idVars)
        }

        public var description: String {
            guard !constraints.isEmpty else {
                return "Solved: \(substitution)"
            }
            var d = "Unsolved (\(constraints.count) constraints left): \(substitution)\n"
            for c in constraints {
                d.append("  --- \(c)\n")
            }
            return d
        }
        
        var solved: Bool {
            return constraints.isEmpty
        }
        
        func process(_ up : UnificationParams, _ strategy : Strategy) -> [Leaf]? {
            for (i, c) in constraints.enumerated() {
                guard let action = strategy(up, c) else { continue }
                var cs = constraints
                cs.remove(at: i)
                cs.append(contentsOf: action.addConstraints)
                let newLeaf = Leaf(substitution, cs, elimVars.union(action.addElimVars), idVars.union(action.addIdVars))
                guard let branches = action.branches else { return [newLeaf] }
                var newLeafs : [Leaf] = []
                for subst in branches {
                    guard let l = newLeaf.substitute(subst) else { continue }
                    newLeafs.append(l)
                }
                return newLeafs
            }
            return nil
        }
        
        func finish(_ domain : Set<Var>) -> Leaf {
            var s = substitution
            s.restrict(domain)
            return Leaf(s, constraints, elimVars, idVars)
        }
        
    }
    
    public struct UnificationParams {
        public let kernelContext : KernelContext
        public let fresh : Fresh
        public let domain : Set<Var>
        public let sizeLimit : Int
    }
        
    public static func unify(_ up : UnificationParams, constraints : [Constraint], strategies : [Strategy]) -> [Leaf] {
        var leafs : [Leaf] = [Leaf(constraints: constraints)]
        var changed = true
        var finished : [Leaf] = []
        while changed {
            changed = false
            var newLeafs : [Leaf] = []
        nextLeaf:
            for leaf in leafs {
                if leaf.size <= up.sizeLimit {
                    for strategy in strategies {
                        if let processed = leaf.process(up, strategy) {
                            newLeafs.append(contentsOf: processed)
                            changed = true
                            continue nextLeaf
                        }
                    }
                }
                finished.append(leaf.finish(up.domain))
            }
            leafs = newLeafs
        }
        return finished
    }
    
    public static func unify(kernelContext : KernelContext, lhs : Tm, rhs : Tm) -> [Leaf] {
        let sizeLimit = (lhs.size + rhs.size + 1) * 10
        
        var freeVars = FreeVars()
        var frees = FreeVars()
        
        for t in [lhs, rhs] {
            guard frees.add(t) else { return [] }
            freeVars.add(t)
        }
        
        func fresh(_ v : Var, _ arity : Int) -> Var {
            return frees.addFresh(v, arity: arity)
        }
        
        let up = UnificationParams(kernelContext: kernelContext, fresh: fresh, domain: freeVars.vars, sizeLimit: sizeLimit)
        
        let constraint = Constraint(level: 0, lhs: lhs, rhs: rhs)
        
        return unify(up, constraints: [constraint], strategies: strategies)
    }

    public static func trivialStrategy(_ up : UnificationParams, _ constraint : Constraint) -> Action? {
        return constraint.isTrivial ? .succeed : nil
    }
    
    public static func rigidRigidStrategy(_ up : UnificationParams, _ constraint : Constraint) -> Action? {
        switch (constraint.lhs, constraint.rhs) {
        case let (.const(c1, binders1, params1), .const(c2, binders2, params2)):
            guard c1 == c2 && binders1.count == binders2.count && params1.count == params2.count else {
                return .fail
            }
            var cs : [Constraint] = []
            let level = constraint.level + binders1.count
            for (i, p1) in params1.enumerated() {
                let p2 = params2[i]
                cs.append(Constraint(level: level, lhs: p1, rhs: p2))
            }
            return Action(addConstraints: cs)
        case let (.bound(b1), .bound(b2)): return b1 == b2 ? .succeed : .fail
        case (.const, .bound): return .fail
        case (.bound, .const): return .fail
        default: return nil
        }
    }
    
    public static func firstOrderStrategy(_ up : UnificationParams, _ constraint : Constraint) -> Action? {
        switch (constraint.lhs, constraint.rhs) {
        case let (tm, .free(v, params: [])) where !tm.freeVars().contains(v):
            guard let tm = tm.toZeroLevel(level: constraint.level) else { return .fail }
            let twh = TmWithHoles(holes: 0, tm)
            return .branch([], v, [twh])
        case let (.free(v, params: []), tm) where !tm.freeVars().contains(v):
            guard let tm = tm.toZeroLevel(level: constraint.level) else { return .fail }
            let twh = TmWithHoles(holes: 0, tm)
            return .branch([], v, [twh])
        case let (.const, .free(v, params: [])) where constraint.lhs.occursForSure(v):
            return .fail
        case let (.free(v, params: []), .const) where constraint.rhs.occursForSure(v):
            return .fail
        default: return nil
        }
    }
    
    public static func patternStrategy(_ up : UnificationParams, _ constraint : Constraint) -> Action? {
        func formsHigherOrderPattern(level : Int, params: [Tm]) -> Bool {
            guard (params.allSatisfy { p in p.isBound(level: level) }) else { return false }
            return Set(params).count == params.count
        }
        switch (constraint.lhs, constraint.rhs) {
        case let (.free(v1, params: params1), .free(v2, params: params2)) where
            formsHigherOrderPattern(level: constraint.level, params: params1) &&
            formsHigherOrderPattern(level: constraint.level, params: params2):
            if v1 == v2 {
                guard params1.count == params2.count else { return .fail }
                var deps : [Int] = []
                for (i, p) in params1.enumerated() {
                    if p == params2[i] {
                        deps.append(i)
                    }
                }
                let H = up.fresh(v1, deps.count)
                let twh = TmWithHoles.hoPattern(holes: params1.count, deps: deps, fresh: H)
                return .branch([], v1, [twh])
            } else {
                var bvars1 : Set<Int> = []
                var bvars2 : Set<Int> = []
                for p in params1 { bvars1.insert(p.boundIndex!) }
                for p in params2 { bvars2.insert(p.boundIndex!) }
                let bvars = Array(bvars1.intersection(bvars2))
                let deps1 = bvars.map { v in params1.firstIndex { p in p.boundIndex! == v }! }
                let deps2 = bvars.map { v in params2.firstIndex { p in p.boundIndex! == v }! }
                let H = up.fresh(v1, bvars.count)
                let twh1 = TmWithHoles.hoPattern(holes: params1.count, deps: deps1, fresh: H)
                let twh2 = TmWithHoles.hoPattern(holes: params2.count, deps: deps2, fresh: H)
                let subst = TmSubstitution(free: [v1 : twh1, v2 : twh2])
                return Action(branches: [subst])
            }
        default: return nil
        }
    }

    public static func rigidFreeStrategy(_ up : UnificationParams, _ constraint : Constraint) -> Action? {
        func couldMatch(pattern : Tm, const : Const) -> Bool {
            switch pattern {
            case .free: return true
            case .bound: return false
            case let .const(c, binders: _, params: _): return c == const
            }
        }

        func couldMatch(pattern : Tm, bound index : Int) -> Bool {
            return pattern == .bound(index)
        }
        
        func couldMatch(pattern : Tm, constBound index : Int) -> Bool {
            switch pattern {
            case .free: return true
            case let .bound(i): return i == index
            case .const: return false
            }
        }
        
        switch (constraint.lhs, constraint.rhs) {
        case let (.const(c, _, params: _), .free(v, params: params)):
            guard let head = up.kernelContext.constants[c]?.head else { return .fail }
            var twhs : [TmWithHoles] = []
            let twh = TmWithHoles.constant(holes: params.count, head: head) { v, a in up.fresh(v, a) }
            twhs.append(twh)
            for (i, p) in params.enumerated() {
                if couldMatch(pattern: p, const: c) {
                    twhs.append(TmWithHoles.projection(holes: params.count, i))
                }
            }
            return .branch([constraint], v, twhs)
        case let (.bound(index), .free(v, params: params)) where index < constraint.level:
            var twhs : [TmWithHoles] = []
            for (i, p) in params.enumerated() {
                if couldMatch(pattern: p, bound: index) {
                    twhs.append(TmWithHoles.projection(holes: params.count, i))
                }
            }
            return .branch([constraint], v, twhs)
        case let (.bound(index), .free(v, params: params)) where index >= constraint.level:
            var twhs : [TmWithHoles] = []
            twhs.append(TmWithHoles.constant(holes: params.count, index - constraint.level))
            for (i, p) in params.enumerated() {
                if couldMatch(pattern: p, constBound: index) {
                    twhs.append(TmWithHoles.projection(holes: params.count, i))
                }
            }
            return .branch([constraint], v, twhs)
        default: return nil
        }
    }

    public static func freeRigidStrategy(_ up : UnificationParams, _ constraint : Constraint) -> Action? {
        return rigidFreeStrategy(up, constraint.reversed)
    }

    public static func freeFreeStrategy(_ up : UnificationParams, _ constraint : Constraint) -> Action? {
        switch (constraint.lhs, constraint.rhs) {
        default: return nil
        }
    }

    public static let strategies : [Strategy] = [
        trivialStrategy,
        rigidRigidStrategy,
        firstOrderStrategy,
        patternStrategy,
        rigidFreeStrategy,
        freeRigidStrategy,
        freeFreeStrategy
    ]

}
