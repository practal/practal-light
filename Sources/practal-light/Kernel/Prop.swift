//
//  Prop.swift
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
    
    public init(hyp : Term?, _ concls : [Term]) {
        self.concls = concls
        if let h = hyp {
            self.hyps = [h]
        } else {
            self.hyps = []
        }
    }
    
    public init(hyps : [Term] = [], _ concl : Term) {
        self.hyps = hyps
        self.concls = [concl]
    }
    
    public init(hyp : Term?, _ concl : Term) {
        self.init(hyp: hyp, [concl])
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
    
    public func flatten() -> Term {
        if isSimple { return concls.first! }
        let Concl = Term.mk_ands(concls)
        if hyps.isEmpty {
            return Concl
        } else {
            let Hyp = Term.mk_ands(hyps)
            return Term.mk_imp(Hyp, Concl)
        }
    }
    
}
