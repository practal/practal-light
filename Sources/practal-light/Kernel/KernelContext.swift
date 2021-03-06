//
//  KernelContext.swift
//  
//
//  Created by Steven Obua on 05/08/2021.
//

import Foundation

public typealias Prop = Term

public struct Theorem : Hashable {
    
    public let kc_uuid : UUID
    
    public let prop : Term
        
    fileprivate init(kc_uuid : UUID, prop : Prop) {
        self.kc_uuid = kc_uuid
        self.prop = prop
    }
    
}

public struct KernelContext : Hashable, CustomStringConvertible {
    
    public typealias Prover = (KernelContext, Prop) -> Theorem?
        
    public enum Ext : Hashable {
        case assume(Term)
        case declare(head: Head)
        case define(const: Const, hyps: [Term], body: Term)
        case seal(const: Const)
        case choose(Const, where: Term)
        case join(parents : [UUID])
    }

    public struct DefCase : Hashable {
        
        public let hyps : [Term]
    
        public let body : Term
        
    }
    
    public struct Def : Hashable {
        
        public let head : Head
                
        public var definitions : [DefCase]
        
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
                
    public func isValid(_ th : Theorem) -> Bool {
        return th.kc_uuid == uuid
    }
    
    private func prove(_ prover : Prover, _ prop : Prop) -> Bool {
        guard let th = prover(self, prop) else { return false }
        guard isValid(th) else {
            return false
        }
        return alpha_equivalent(prop, th.prop)
    }
    
    private func prove(_ prover : Prover, _ props : [Prop]) -> Bool {
        return props.allSatisfy { prop in prove(prover, prop) }
    }

    private func extend(_ addExtensions : [Ext], addAxioms : [Term] = [], mergeConstants : [Const : Def] = [:]) -> KernelContext {
        let mergedConstants = constants.merging(mergeConstants) { old, new in new }
        return KernelContext(parent: uuid, extensions: addExtensions, axioms: axioms + addAxioms, constants: mergedConstants)
    }
    
    public func assume(_ term : Term) -> KernelContext? {
        //print("assume \(term)")
        guard isWellformed(term) else { return nil }
        //guard prove(prover, Term.mk_in_Prop(term)) else { return nil }
        return extend([.assume(term)], addAxioms: [term])
    }
            
    public func axiom(_ index : Int) -> Theorem {
        return Theorem(kc_uuid: uuid, prop: axioms[index])
    }
    
    public func declare(head : Head) -> KernelContext?
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
        guard var def = constants[const], !def.sealed else { return nil }
        for t in hyps + [body] {
            guard let frees = checkWellformedness(t)?.arity else { return nil }
            guard def.head.covers(frees) else { return nil }
        }
        var props : [Term] = []
        /*for h in hyps {
            props.append(Term.mk_in_Prop(h))
        }*/
        for d in def.definitions {
            let compatible = Term.mk_prop(hyps: d.hyps + hyps, Term.mk_eq(d.body, body))
            props.append(compatible)
        }
        guard prove(prover, props) else { return nil }
        let ax : Prop = .mk_prop(hyps: hyps, Term.mk_eq(def.head.term, body))
        def.definitions.append(DefCase(hyps: hyps, body: body))
        return extend([.define(const: const, hyps: hyps, body: body)], addAxioms: [ax], mergeConstants: [const: def])
    }
        
    public func choose(const : Const, from: Theorem) -> KernelContext? {
        guard isValid(from) else { return nil }
        guard constants[const] == nil else { return nil }
        guard let (v, body) = Term.dest_ex(from.prop) else { return nil }
        let cond = Term.replace(kc: self, free: v, with: const, in: body)
        guard let frees = checkWellformedness(cond)?.arity, frees.isEmpty else {
            print("choose: free variables discovered")
            return nil
        }
        let head = Head(const: const, binders: [], params: [])!
        let def = Def(head: head, definitions: [], sealed: true)
        return extend([.choose(const, where: cond)], addAxioms: [cond], mergeConstants: [const : def])
    }
    
    public static func join(parents : [KernelContext]) -> KernelContext? {
        var axioms : [Term] = []
        var constants : [Const : Def] = [:]
        for parent in parents {
            for (const, def) in parent.constants {
                if let d = constants[const] {
                    guard d == def else { return nil }
                } else {
                    constants[const] = def
                }
            }
            for axiom in parent.axioms {
                if !axioms.contains(axiom) {
                    axioms.append(axiom)
                }
            }
        }
        let extensions : [Ext] = [.join(parents: parents.map { p in p.uuid})]
        return KernelContext(parent: nil, extensions: extensions, axioms: axioms, constants: constants)
    }
    
    public var lastAxiom : Theorem {
        return axiom(axioms.count - 1)
    }
    
    private static func findOpeningDeclaration(const : Const, from : Int, extensions : [Ext]) -> Int? {
        var i = from
        while i >= 0 {
            switch extensions[i] {
            case .assume, .choose, .join: return nil
            case let .seal(c):
                if c != const { return nil }
            case let .declare(head: head):
                if head.const != const { return nil }
                else { return i }
            case let .define(const: c, hyps: _, body: _):
                if c != const { return nil }
            }
            i -= 1
        }
        return nil
    }
    
    public static func lift(_ th : Theorem, in chain : KCChain, from : Int, to : Int) -> Theorem? {
        guard chain.isValidIndex(from) && chain.isValidIndex(to) else { return nil }
        guard chain[from].uuid == th.kc_uuid else { return nil }
        if from == to { return th }
        else if from < to  {
            return Theorem(kc_uuid: chain[to].uuid, prop: th.prop)
        } else {
            var current = th.prop
            let exts = chain.extensions(from: to+1, to: from)
            let constants = chain[from].constants
            var i = exts.count - 1
            while i >= 0 {
                //print("lift at \(i)): \(current)")
                switch exts[i] {
                case let .assume(hyp):
                    let (frees, arity) = chain[from].freeVarsOf(hyp)
                    for (_, a) in arity {
                        if a != 0 { return nil }
                    }
                    current = Term.mk_imp(Term.mk_all(frees, hyp), current)
                case let .choose(c, where: _):
                    if current.contains(const: c) {
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
                case let .define(const: const, hyps: hyps, body: body):
                    guard let head = constants[const]?.head, head.binders.count == 0  else { return nil }
                    let d = Prop.mk_prop(hyps: hyps, Term.mk_eq(head.term, body))
                    let vars = head.params.map { p in p.unappliedVar! }
                    current = Term.mk_imp(Term.mk_all(vars, d), current)
                case let .seal(const: const):
                    if !current.contains(const: const), let declIndex = findOpeningDeclaration(const: const, from: i, extensions: exts) {
                        i = declIndex
                    }
                case .join: break
                }
                i -= 1
            }
            return Theorem(kc_uuid: chain[to].uuid, prop: current)
        }
    }
        
    public func substituteSafely(_ substitution : TmSubstitution, in term : Term) -> Term? {
        guard let tm = Tm.fromWellformedTerm(self, term: term) else { return nil }
        return substitution.apply(tm)?.term()
    }

    public func substituteSafely(_ substitution : TmSubstitution, in terms : [Term]) -> [Term]? {
        let sterms = terms.compactMap { t in substituteSafely(substitution, in: t) }
        guard sterms.count == terms.count else { return nil }
        return sterms
    }

    public func substitute(_ substitution : Substitution, in thm : Theorem) -> Theorem? {
        guard isValid(thm) else { return nil }
        guard let subst = TmSubstitution(self, wellformed: substitution) else { return nil }
        guard let prop = substituteSafely(subst, in: thm.prop) else { return nil }
        return Theorem(kc_uuid: uuid, prop: prop)
    }
    
    public func substitute(_ subst : TmSubstitution, in thm : Theorem) -> Theorem? {
        guard isValid(thm) else { return nil }
        guard isWellformed(subst) else { return nil }
        guard let prop = substituteSafely(subst, in: thm.prop) else { return nil }
        return Theorem(kc_uuid: uuid, prop: prop)

    }
    
    private func mk_thm(_ prop : Term) -> Theorem {
        return Theorem(kc_uuid: uuid, prop: prop)
    }
    
    public func modusPonens(_ hyp : Theorem, _ imp : Theorem) -> Theorem? {
        guard isValid(hyp), isValid(imp) else { return nil }
        guard let (op, left, right) = Term.dest_binary(imp.prop), op == .c_imp else { return nil }
        guard alpha_equivalent(hyp.prop, left) else { return nil }
        return mk_thm(right)
    }
    
    public func allIntro(_ x : Var, _ thm : Theorem) -> Theorem? {
        guard isValid(thm) else { return nil }
        return mk_thm(.mk_all(x, thm.prop))
    }

    public static func root() -> KernelContext {
        var kc = KernelContext(parent: nil, extensions: [], axioms: [], constants: [:])
        
        func introduce(_ const : Const, binders : [Var] = [], params : Term...) {
            kc = kc.declare(head: .init(const: const, binders: binders, params: params)!)!
        }
        func v(_ name : String) -> Var {
            return Var(name)!
        }
        func tv(_ name : String, _ params : Term...) -> Term {
            return .variable(Var(name)!, params: params)
        }
        
        //introduce(.c_Prop)
        introduce(.c_eq, params: tv("x"), tv("y"))
        //introduce(.c_in, params: tv("x"), tv("T"))
        introduce(.c_and, params: tv("p"), tv("q"))
        introduce(.c_imp, params: tv("p"), tv("q"))
        introduce(.c_ex, binders: [v("x")], params: tv("P", tv("x")))
        introduce(.c_all, binders: [v("x")], params: tv("P", tv("x")))
        
        /*kc = kc.assume(.mk_in_Prop(.mk_in(tv("x"), tv("T")))) { kc, prop in
            guard kc.isWellformed(prop) else { return nil }
            return Theorem(kc_uuid: kc.uuid, prop: prop)
        }!*/
        
        return kc
    }
    
    public var description: String {
        var s = "KernelContext \(uuid), parent: \(parent?.description ?? "none")\n"
        s.append("  Extensions:\n")
        for e in extensions {
            s.append("  - \(e)\n")
        }
        s.append("  Constants:\n")
        for c in constants {
            s.append("  - \(c.key): \(c.value)\n")
        }
        s.append("  Axioms:\n")
        for a in axioms {
            s.append("  - \(a)\n")
        }
        return s
    }
                    
}

