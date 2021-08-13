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

public struct Prover {
    
    public static let fail = seq()
    
    public static let byAxioms : ContextProver = ProveByAxioms()
    
    public static func seq(_ provers : ContextProver...) -> ContextProver {
        return ContextProvers(provers: provers)
    }
    
    public static func from(_ prover : @escaping KernelContext.Prover) -> ContextProver {
        return KernelProver(prover: prover)
    }

}

