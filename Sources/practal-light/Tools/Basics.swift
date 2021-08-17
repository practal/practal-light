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
        let prover = Prover.seq(Prover.byAxioms, Prover.byStoredTheorems)
        return prover.prove(self, prop)
    }
    
    public func all(_ vars : String..., thm : Theorem) -> Theorem? {
        var thm = thm
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
    
}
