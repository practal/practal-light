//
//  Kernel.swift
//  
//
//  Created by Steven Obua on 05/08/2021.
//

import Foundation

public struct Prop : Hashable {
    
    public var hyps : [Term]
    
    public var concls : [Term]

    public init(hyps : [Term] = [], _ concls : [Term]) {
        self.hyps = hyps
        self.concls = concls
    }
    
    public init(hyps : [Term] = [], _ concl : Term) {
        self.hyps = hyps
        self.concls = [concl]
    }
    
    public var hasHyps : Bool {
        return !hyps.isEmpty
    }
    
    public var concl : Term? {
        guard concls.count == 1 else { return nil }
        return concls.first!
    }
    
    public var isSimple : Bool {
        return hyps.isEmpty && concls.count == 1
    }
    
    public func mkSimple() -> Prop {
        if isSimple { return self }
        let Concl = Term.mk_ands(concls)
        if hyps.isEmpty {
            return Prop(Concl)
        } else {
            let Hyp = Term.mk_ands(hyps)
            return Prop(Term.mk_imp(Hyp, Concl))
        }
    }
    
}

public struct Theorem : Hashable {
    
    public let kc_uuid : UUID
    
    public let prop : Prop
        
    fileprivate init(kc_uuid : UUID, prop : Prop) {
        self.kc_uuid = kc_uuid
        self.prop = prop
    }
    
}

public enum KCExt {
    case assume(Term)
    case declare(head: Head)
    case narrow(const: Const, frame: Term)
    case define(const: Const, hyps: [Term], body: Term)
    case choose(Const, exists: Term)
}

public struct KernelContext {
    
    public typealias Prover = (KernelContext, Prop) -> Theorem?
        
    public struct Def {
        
        public var head : Head
        
        public var frame : Term?
        
        public var definitions : [(hyps : [Term], body : Term)]
            
    }
    
    public let uuid : UUID

    public let extends : (parent: UUID, extensions: [KCExt])?
            
    public let axioms : [Term]
    
    public let constants : [Const : Def]
    
    private init(uuid : UUID = UUID(), parent: UUID, extensions: [KCExt], axioms : [Term], constants : [Const : Def]) {
        self.extends = (parent, extensions)
        self.uuid = uuid
        self.axioms = axioms
        self.constants = constants
    }
    
    private init(uuid : UUID = UUID()) {
        self.extends = nil
        self.uuid = uuid
        self.axioms = []
        self.constants = [:]
    }
        
    public func refl(_ term : Term) -> Theorem? {
        guard isWellformed(term) else { return nil }
        let prop = Prop(Term.mk_eq(term, term))
        return Theorem(kc_uuid: uuid, prop: prop)
    }
    
    public func isValid(_ th : Theorem) -> Bool {
        return th.kc_uuid == uuid
    }
    
    private func prove(_ prover : Prover, _ prop : Term) -> Bool {
        let prop = Prop(prop)
        guard let th = prover(self, prop) else { return false }
        guard isValid(th) else { return false }
        return prop == th.prop
    }
    
    private func extend(_ addExtensions : [KCExt] = [], _ addAxioms : [Term] = [], _ mergeConstants : [Const : Def] = [:]) -> KernelContext {
        let addedExtensions = (extends?.extensions ?? []) + addExtensions
        let mergedConstants = constants.merging(mergeConstants) { old, new in new }
        return KernelContext(parent: uuid, extensions: addedExtensions, axioms: axioms + addAxioms, constants: mergedConstants)
    }
    
    /// Adds an axiom.
    @discardableResult
    public mutating func assume(_ term : Term, prover : Prover) -> KernelContext? {
        guard let frees = checkWellformedness(term) else { return nil }
        guard frees.isEmpty else { return nil }
        guard prove(prover, Term.mk_in_Prop(term)) else { return nil }
        return extend([.assume(term)])
    }
            
    public func axiom(_ index : Int) -> Theorem {
        let prop = Prop(axioms[index])
        return Theorem(kc_uuid: uuid, prop: prop)
    }
                
}
