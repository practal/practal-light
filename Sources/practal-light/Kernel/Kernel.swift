//
//  Kernel.swift
//  
//
//  Created by Steven Obua on 05/08/2021.
//

import Foundation

public struct Theorem : Hashable {
    
    public let kc_uuid : UUID
    
    public let prop : Prop
        
    fileprivate init(kc_uuid : UUID, prop : Prop) {
        self.kc_uuid = kc_uuid
        self.prop = prop
    }
    
}

public struct KernelContext {
    
    public typealias Prover = (KernelContext, Prop) -> Theorem?
        
    public enum Ext {
        case assume(Term)
        case declare(head: Head)
        case define(const: Const, hyps: [Term], body: Term)
        case seal(const: Const)
        case choose(Const, where: Term)
    }

    public struct Def {
        
        public let head : Head
                
        public var definitions : [(hyps : [Term], body : Term)]
        
        public var sealed : Bool
            
    }
    
    public let uuid : UUID

    public let parent : UUID?
    
    public let extensions : [Ext]
            
    public let axioms : [Term]
    
    public let constants : [Const : Def]
    
    private init(uuid : UUID = UUID(), parent: UUID?, extensions: [Ext], axioms : [Term], constants : [Const : Def]) {
        self.parent = parent
        self.extensions = extensions
        self.uuid = uuid
        self.axioms = axioms
        self.constants = constants
    }
        
    public init?<S:Collection>(squash contexts: S) where S.Element == KernelContext {
        guard !contexts.isEmpty else { return nil }
        var exts : [Ext] = []
        var last : KernelContext? = nil
        for context in contexts {
            guard last == nil || last!.uuid == context.parent else { return nil }
            exts.append(contentsOf: context.extensions)
            last = context
        }
        self.parent = contexts.first!.parent
        self.uuid = last!.uuid
        self.axioms = last!.axioms
        self.constants = last!.constants
        self.extensions = exts
    }
            
    public func refl(_ term : Term) -> Theorem? {
        guard isWellformed(term) else { return nil }
        let prop = Prop(Term.mk_eq(term, term))
        return Theorem(kc_uuid: uuid, prop: prop)
    }
    
    public func isValid(_ th : Theorem) -> Bool {
        return th.kc_uuid == uuid
    }
    
    private func prove(_ prover : Prover, _ prop : Prop) -> Bool {
        if prop.concls.isEmpty { return true }
        guard let th = prover(self, prop) else { return false }
        guard isValid(th) else { return false }
        return prop == th.prop
    }

    private func prove(_ prover : Prover, _ prop : Term) -> Bool {
        return prove(prover, Prop(prop))
    }
    
    private func prove(_ prover : Prover, _ props : [Term]) -> Bool {
        return prove(prover, Prop(props))
    }

    private func extend(_ addExtensions : [Ext], addAxioms : [Term] = [], mergeConstants : [Const : Def] = [:]) -> KernelContext {
        let mergedConstants = constants.merging(mergeConstants) { old, new in new }
        return KernelContext(parent: uuid, extensions: extensions + addExtensions, axioms: axioms + addAxioms, constants: mergedConstants)
    }
    
    public func assume(_ term : Term, prover : Prover) -> KernelContext? {
        guard let frees = checkWellformedness(term) else { return nil }
        guard frees.isEmpty else { return nil }
        guard prove(prover, Term.mk_in_Prop(term)) else { return nil }
        return extend([.assume(term)], addAxioms: [term])
    }
            
    public func axiom(_ index : Int) -> Theorem {
        let prop = Prop(axioms[index])
        return Theorem(kc_uuid: uuid, prop: prop)
    }
    
    public func declare(head : Head, prover : Prover) -> KernelContext?
    {
        guard constants[head.const] == nil else { return nil }
        let def = Def(head: head, definitions: [], sealed : false)
        return extend([.declare(head: head)], mergeConstants: [head.const : def])
    }
    
    public func seal(const : Const) -> KernelContext? {
        guard var def = constants[const], !def.sealed else { return nil }
        def.sealed = true
        return extend([.seal(const: const)], mergeConstants: [const : def])
    }
    
    public func define(const : Const, hyps : [Term], body : Term, prover : Prover) -> KernelContext? {
        guard let def = constants[const], !def.sealed else { return nil }
        for t in hyps + [body] {
            guard let frees = checkWellformedness(t) else { return nil }
            guard def.head.covers(frees) else { return nil }
        }
        var props : [Term] = []
        for h in hyps {
            props.append(Term.mk_in_Prop(h))
        }
        for d in def.definitions {
            let compatible = Prop(hyps: d.hyps + hyps, Term.mk_eq(d.body, body))
            props.append(compatible.flatten())
        }
        guard prove(prover, Prop(props)) else { return nil }
        let ax = Prop(hyps: hyps, Term.mk_eq(def.head.term, body)).flatten()
        return extend([.define(const: const, hyps: hyps, body: body)], addAxioms: [ax])
    }
    
    public func setDomain(const : Const, domain : Term, prover : Prover) -> KernelContext? {
        let hyp = Term.mk_not(domain)
        let body = Term.c_nil
        return define(const: const, hyps: [hyp], body: body, prover: prover)
    }
    
    public func choose(const : Const, where cond: Term, prover : Prover) -> KernelContext? {
        guard constants[const] == nil else { return nil }
        let fresh = Term.fresh(const.name, for: cond)
        let replaced = Term.replace(const: const, with: fresh, in: cond)
        let exists = Term.mk_ex(fresh, replaced)
        guard let frees = checkWellformedness(exists), frees.isEmpty else { return nil }
        guard prove(prover, exists) else { return nil }
        let head = Head(const: const, binders: [], params: [])!
        let def = Def(head: head, definitions: [], sealed: true)
        return extend([.choose(const, where: cond)], addAxioms: [cond], mergeConstants: [const : def])
    }
    
    public static func lift(_ th : Theorem, in chain : KCChain, from : Int, to : Int) -> Theorem? {
        guard chain.isValidIndex(from) && chain.isValidIndex(to) else { return nil }
        guard chain[from].uuid == th.kc_uuid else { return nil }
        if from == to { return th }
        else if from < to  {
            return Theorem(kc_uuid: chain[to].uuid, prop: th.prop)
        } else {
            var current = th.prop.flatten()
            let exts = chain.extensions(from: to+1, to: from)
            var i = exts.count - 1
            while i >= 0 {
                switch exts[i] {
                case let .assume(hyp):
                    current = Term.mk_imp(hyp, current)
                case let .choose(c, where: _):
                    if current.arityOf(const: c) != nil {
                        let v = Term.fresh(c.name, for: current)
                        current = Term.mk_ex(v, Term.replace(const: c, with: v, in: current))
                    }
                case let .declare(head: head):
                    let c = head.const
                    if let arity = current.arityOf(const: c) {
                        guard arity.binders == 0 else { return nil }
                        let v = Term.fresh(c.name, for: current)
                        current = Term.replace(const: c, with: v, in: current)
                    }
                default:
                    return nil
                }
                i -= 1
            }
            return Theorem(kc_uuid: chain[to].uuid, prop: Prop(current))
        }
    }
                    
}

