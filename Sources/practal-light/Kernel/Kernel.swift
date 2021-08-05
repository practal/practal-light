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
    
}

public struct CProp : Hashable {
    
    public let kernel_uuid : UUID
    
    public let prop : Prop
        
    fileprivate init(kernel_uuid : UUID, prop : Prop) {
        self.kernel_uuid = kernel_uuid
        self.prop = prop
    }
    
}

public struct Theorem : Hashable {
    
    public let kernel_uuid : UUID
    
    public let prop : Prop
        
    fileprivate init(kernel_uuid : UUID, prop : Prop) {
        self.kernel_uuid = kernel_uuid
        self.prop = prop
    }
    
}

public struct CTerm : Hashable {
    
    public let kernel_uuid : UUID
    
    public let term : Term
    
    public let freeVars : [Var : Int]?
        
    fileprivate init(kernel_uuid : UUID, term : Term, freeVars : [Var : Int]?) {
        self.kernel_uuid = kernel_uuid
        self.term = term
        self.freeVars = freeVars
    }
        
    public func refl() -> Theorem {
        let prop = Prop(Term.mk_eq(term, term))
        return Theorem(kernel_uuid: kernel_uuid, prop: prop)
    }
        
}

public struct Kernel {
    
    public let uuid = UUID()
    
    public typealias Prover = (CProp) -> Theorem
    
    public enum Result {
        case succeeded
        case failed
    }
    
    public struct Def {
        
        public var head : Head
        
        public var frame : Term?
        
        public var definitions : [(hyps : [Term], body : Term)]
        
        public var sealed : Bool
    
    }
        
    private var _axioms : [Term]
    
    private var _constants : [Const : Def]
    
    private init() {
        self._axioms = []
        self._constants = [:]
    }
    
    /// Certifies that `term` is wellformed.
    public func certify(_ term : Term) -> CTerm? {
        guard let fvs = checkWellformedness(term) else { return nil }
        return CTerm(kernel_uuid: uuid, term: term, freeVars: fvs)
    }
        
    /// Adds an axiom.
    @discardableResult
    public mutating func assume(_ prop : CProp) -> Result {
        guard prop.prop.isSimple else { return .failed }
        let a = prop.prop.concl!
        _axioms.append(a)
        return .succeeded
    }
    
    public func defOf(_ const : Const) -> Def? {
        return _constants[const]
    }
    
    public var countAxioms : Int { return _axioms.count }
    
    public func axiom(_ index : Int) -> Theorem {
        let prop = Prop(_axioms[index])
        return Theorem(kernel_uuid: uuid, prop: prop)
    }
    
    public func ensureFreeVars(_ cterm : CTerm) -> CTerm {
        guard cterm.freeVars == nil else { return cterm }
        guard cterm.kernel_uuid == uuid else { fatalError() }
        let fvs = freeVarsOf(cterm.term)
        return CTerm(kernel_uuid: uuid, term: cterm.term, freeVars: fvs)
    }
            
}
