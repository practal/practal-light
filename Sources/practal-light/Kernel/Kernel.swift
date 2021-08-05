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
        case narrow(const: Const, frame: Term)
        case define(const: Const, hyps: [Term], body: Term)
        case choose(Const, exists: Term)
    }

    public struct Def {
        
        public var head : Head
        
        public var frame : Term?
        
        public var definitions : [(hyps : [Term], body : Term)]
            
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
    
    private func prove(_ prover : Prover, _ prop : Term) -> Bool {
        let prop = Prop(prop)
        guard let th = prover(self, prop) else { return false }
        guard isValid(th) else { return false }
        return prop == th.prop
    }
    
    private func extend(_ addExtensions : [Ext] = [], _ addAxioms : [Term] = [], _ mergeConstants : [Const : Def] = [:]) -> KernelContext {
        let mergedConstants = constants.merging(mergeConstants) { old, new in new }
        return KernelContext(parent: uuid, extensions: extensions + addExtensions, axioms: axioms + addAxioms, constants: mergedConstants)
    }
    
    /// Adds an axiom.
    public func assume(_ term : Term, prover : Prover) -> KernelContext? {
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

