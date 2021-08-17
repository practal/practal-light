//
//  Prover.swift
//  
//
//  Created by Steven Obua on 13/08/2021.
//

import Foundation

public protocol ContextProver {
    
    func prove(_ context : Context, _ prop : Prop) -> Theorem?
    
}

fileprivate struct ContextProvers  : ContextProver {
    let provers : [ContextProver]
    
    func prove(_ context: Context, _ prop: Prop) -> Theorem? {
        for prover in provers {
            if let thm = prover.prove(context, prop) { return thm }
        }
        return nil
    }
}

fileprivate struct KernelProver : ContextProver {
    let prover : KernelContext.Prover
    
    func prove(_ context : Context, _ prop : Prop) -> Theorem? {
        return prover(context.kernel, prop)
    }
}

fileprivate struct ProveByAxioms : ContextProver {
    func prove(_ context: Context, _ prop: Prop) -> Theorem? {
        let matching = Matching(kc: context.kernel)
        return matching.proveByAxiom(term: prop)?.thm
    }
}

fileprivate struct ProveByStoredTheorems : ContextProver {
    func prove(_ context: Context, _ prop: Prop) -> Theorem? {
        let kc = context.kernel
        let matching = Matching(kc: kc)
        guard let prop = kc.tmOf(prop) else { return nil }
        for (_, thm) in context.storedTheorems {
            let stored = kc.tmOf(thm.prop)!
            guard let subst = matching.match1(pattern: stored, instance: prop) else { continue }
            guard let th = kc.substitute(subst, in: context.lift(thm)!) else { continue }
            return th
        }
        return nil
    }
}

fileprivate struct DebugProver : ContextProver {
    let prover : ContextProver
    func prove(_ context: Context, _ prop : Prop) -> Theorem? {
        print("proof obligation: \(prop)")
        if let th = prover.prove(context, prop) {
            print("proved successfully")
            return th
        } else {
            print("could not prove")
            return nil
        }
    }
}

public struct Prover {
    
    public static let fail = seq()
    
    public static let byAxioms : ContextProver = ProveByAxioms()
    
    public static let byStoredTheorems : ContextProver = ProveByStoredTheorems()
    
    public static func seq(_ provers : ContextProver...) -> ContextProver {
        return ContextProvers(provers: provers)
    }
    
    public static func from(_ prover : @escaping KernelContext.Prover) -> ContextProver {
        return KernelProver(prover: prover)
    }
    
    public static func debug(_ prover : ContextProver) -> ContextProver {
        return DebugProver(prover: prover)
    }

}

