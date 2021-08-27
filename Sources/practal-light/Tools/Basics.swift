//
//  Basics.swift
//  
//
//  Created by Steven Obua on 16/08/2021.
//

import Foundation

extension Context {
    
    public func trivial(_ prop : String) -> Theorem? {
        guard let prop = parse(prop) else { return nil }
        return Prover.trivial.prove(self, prop)
    }
    
    public func all(_ vars : String..., thm : Theorem) -> Theorem? {
        var thm = lift(thm)!
        for v in vars.reversed() {
            guard let v = Var(v) else { return nil }
            guard let qthm = kernel.allIntro(v, thm) else { return nil }
            thm = qthm
        }
        return thm
    }
    
    public func match(pattern : Term, instance : Term, max_matches : Int = Int.max) -> [TmSubstitution] {
        let kc = kernel
        let mc = Matching(kc: kc)
        guard let pattern = kc.tmOf(pattern) else { return [] }
        guard let instance = kc.tmOf(instance) else { return [] }
        return mc.match(pattern: pattern, instance: instance, max_matches: max_matches)
    }

    public func match1(pattern : Term, instance : Term, max_matches : Int = Int.max) -> TmSubstitution? {
        return match(pattern: pattern, instance: instance, max_matches: 1).first
    }

    public func match(patterns : [Term], instances : [Term], max_matches : Int = Int.max) -> [TmSubstitution] {
        let kc = kernel
        let mc = Matching(kc: kc)
        let _patterns = patterns.compactMap { t in kc.tmOf(t) }
        let _instances = instances.compactMap { t in kc.tmOf(t) }
        guard _patterns.count == patterns.count && _instances.count == instances.count else { return [] }
        return mc.match(patterns: _patterns, instances: _instances, max_matches: max_matches)
    }

    public func apply(hyp: Theorem, to implication : Theorem) -> Set<Theorem> {
        let hyp = lift(hyp)!
        let implication = lift(implication)!
        guard let (h, _) = Term.dest_binary(implication.prop, op: .c_imp) else { return [] }
        let substs = match(pattern: h, instance: hyp.prop)
        var thms : Set<Theorem> = []
        for subst in substs {
            //print("hyp = \(pretty(hyp.prop)), pattern = \(pretty(h)), subst = \(subst)")
            guard let imp = kernel.substitute(subst, in: implication) else { continue }
            guard let mp = kernel.modusPonens(hyp, imp) else { continue }
            thms.insert(mp)
        }
        return thms
    }
    
    public func apply(_ hyps : [Theorem], goal : Term?, to implication : Theorem) -> Set<Theorem> {
        let hyps = hyps.map { h in lift(h)! }
        let implication = lift(implication)!
        var patterns : [Term] = []
        var instances : [Term] = []
        var target = implication.prop
        for hyp in hyps {
            instances.append(hyp.prop)
            guard let (h, c) = Term.dest_binary(target, op: .c_imp) else { return [] }
            patterns.append(h)
            target = c
        }
        if let g = goal {
            patterns.append(target)
            instances.append(g)
        }
        let substs = match(patterns: patterns, instances: instances)
        var thms : Set<Theorem> = []
    next:
        for subst in substs {
            guard var imp = kernel.substitute(subst, in: implication) else { continue next }
            for h in hyps {
                guard let c = kernel.modusPonens(h, imp) else { continue next }
                imp = c
            }
            thms.insert(imp)
        }
        
        return thms
    }
    
    public func apply(_ hyps : Theorem..., to implication : Theorem) -> Set<Theorem> {
        return apply(hyps, goal : nil, to: implication)
    }
    
    public func apply(_ hyps : Theorem..., goal : String, to implication : Theorem) -> Theorem? {
        guard let goal = parse(goal) else { return nil }
        return apply(hyps, goal : goal, to: implication).first
    }

    public func symmetric(_ thm : Theorem) -> Theorem? {
        guard let sym = trivial("x = y ⟶ y = x") else { return nil }
        return apply(hyp: thm, to: sym).first
    }
    
    public func apply(eq : Theorem, left : Theorem) -> Theorem? {
        let eq_subst = trivial("x = y ⟶ x ⟶ y")!
        guard let a = apply(eq, to: eq_subst).first else { return nil }
        return apply(left, to: a).first
    }
    
    public func apply(eq : Theorem, right : Theorem) -> Theorem? {
        let eq_subst = trivial("x = y ⟶ y ⟶ x")!
        guard let a = apply(eq, to: eq_subst).first else { return nil }
        return apply(right, to: a).first
    }
    
    
    public func instantiate(binding : Term, instances _instances: [Term]) -> (const: Const, params: [Term])? {
        guard let binding = kernel.tmOf(binding) else { return nil }
        let instances = _instances.compactMap { t in kernel.tmOf(t) }
        guard instances.count == _instances.count else { return nil }
        switch binding {
        case let .const(c, binders: binders, params: params) where binders.count == _instances.count:
            let keyValues = (0 ..< instances.count).map { i in (i, TmWithHoles(holes: 0, instances[i])) }
            let dict = Dictionary(uniqueKeysWithValues: keyValues)
            let subst = TmSubstitution(bound: dict)
            guard let params = subst.apply(params) else { return nil }
            return (const: c, params: params.map { p in p.term()! })
        default: return nil
        }
    }
    
    public func instantiate(binding : Term, instance : Term, const : Const) -> Term? {
        guard let (c, params) = instantiate(binding: binding, instances: [instance]) else { return nil }
        guard c == const && params.count == 1 else { return nil }
        return params.first!
    }
    
    public func allElim(_ all : Theorem, _ t : Term) -> Theorem? {
        guard let goal = instantiate(binding: all.prop, instance: t, const: .c_all) else { return nil }
        let ax = trivial("(∀ x. P[x]) ⟶ P[t]")!
        let thms = apply([all], goal: goal, to: ax)
        return thms.first
    }

    public func choose(_ name : String, from: Theorem) -> Theorem? {
        let const = Const("local.\(name)")!
        guard let w = instantiate(binding: from.prop, instance: .constant(const, binders: [], params: []), const: .c_ex) else { return nil }
        guard choose(const: const, where: w, prover: Prover.debug(Prover.fail)) else { return nil }
        return kernel.lastAxiom
    }

}
