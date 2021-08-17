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
    
    public func match(pattern : Term, instance : Term) -> [TmSubstitution] {
        let kc = kernel
        let mc = Matching(kc: kc)
        guard let pattern = kc.tmOf(pattern) else { return [] }
        guard let instance = kc.tmOf(instance) else { return [] }
        return mc.match(pattern: pattern, instance: instance)
    }

    public func apply(hyp: Theorem, to implication : Theorem) -> Theorem? {
        guard let (h, _) = Term.dest_binary(implication.prop, op: .c_imp) else { return nil }
        guard let subst = match(pattern: h, instance: hyp.prop).first else { return nil }
        guard let imp = kernel.substitute(subst, in: implication) else { return nil }
        return kernel.modusPonens(hyp, imp)
    }
    
    public func apply(_ hyps : Theorem..., to implication : Theorem) -> Theorem? {
        var th = implication
        for h in hyps {
            guard let c = apply(hyp: h, to: th) else { return nil }
            th = c
        }
        return th
    }
    
    public func symmetric(_ thm : Theorem) -> Theorem? {
        guard let sym = trivial("x = y ⟶ y = x") else { return nil }
        return apply(hyp: thm, to: sym)
    }
    
}
