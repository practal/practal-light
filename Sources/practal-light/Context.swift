//
//  Context.swift
//  
//
//  Created by Steven Obua on 06/08/2021.
//

import Foundation

public typealias AxiomID = Int

public final class Context {
        
    private var kcc : KCChain
    private var syntax : Syntax
    private var dirty_syntax : Bool
    private var _parser : PractalExprParser
    private var _printer : PrettyPrinter

    fileprivate init(_ kc : KernelContext) {
        kcc = KCChain(kc)
        syntax = []
        dirty_syntax = true
        _parser = PractalExprParser(syntax: syntax)
        _printer = PrettyPrinter(patterns: syntax)
    }
    
    private func refresh() {
        if dirty_syntax {
            _parser = PractalExprParser(syntax: syntax)
            _printer = PrettyPrinter(patterns: syntax)
            dirty_syntax = false
        }
    }
    
    public var kernel : KernelContext {
        return kcc.current
    }
    
    @discardableResult
    public func addSyntax(_ pattern : SyntaxPattern, _ concreteSyntax : ConcreteSyntax) -> Bool {
        guard pattern.isPattern else {
            print("pattern is not a pattern")
            return false
        }
        let vars = pattern.vars()
        let concreteSyntax = concreteSyntax.selectVars { v in vars.contains(v) }
        guard !concreteSyntax.hasDuplicateVarOccurrences else {
            print("concrete syntax has duplicate variable occurrences")
            return false
        }
        guard Set(concreteSyntax.vars).count == vars.count else {
            print("some free variables of the abstract syntax do not occur in the concrete syntax")
            return false
        }
        syntax.append((pattern, [concreteSyntax]))
        //print("Added pattern: \(syntax.last!)")
        dirty_syntax = true
        return true
    }
    
    public var parser : PractalExprParser {
        refresh()
        return _parser
    }
    
    public var printer : PrettyPrinter {
        refresh()
        return _printer
    }
    
    @discardableResult
    public func extend(_ op: (Context) -> KernelContext?) -> Bool {
        guard let kc = op(self) else { return false }
        return kcc.append(kc)
    }
    
}

extension Context {
    
    public func isWellformed(_ term : Term) -> Bool {
        return kernel.isWellformed(term)
    }
    
    public func parse(_ expr : String) -> Term? {
        return parser.parse(expr)
    }
    
    public func pretty(_ term : Term) -> String {
        return printer.printTerm(term)
    }
    
    public func addSyntax(const : Const, syntax : String, priority : ConcreteSyntax.Priority) -> Bool {
        guard let head = kernel.constants[const]?.head else { return false }
        let pattern = SyntaxPattern.from(head.term)
        guard let css = parser.parse(css: syntax) else {
            print("Could not parse concrete syntax spec '\(syntax)'")
            return false
        }
        return addSyntax(pattern, css.withPriority(priority))
    }
    
    public func declare(_ constant : Term) -> Const? {
        guard let head = Head(constant) else { return nil }
        guard (extend { context in
            context.kernel.declare(head: head)
        }) else { return nil }
        return head.const
    }
    
    // todo: make this an atomic operation that either completely fails or completely succeeds
    public func declare(_ constant : String, syntax : [String], priority : ConcreteSyntax.Priority = .None) -> Const? {
        guard let parsed = parse(constant) else { return nil }
        guard let const = declare(parsed) else { return nil }
        for s in syntax {
            guard addSyntax(const: const, syntax: s, priority: priority) else { return nil }
        }
        return const
    }
    
    public func assume(_ prop : Term, prover : ContextProver = Prover.fail) -> AxiomID? {
        guard (extend { context in
            context.kernel.assume(prop) { _, prop in
                prover.prove(context, prop)
            }
        }) else { return nil }
        return kernel.axioms.count - 1
    }
    
    public func assume(_ prop : String, prover : ContextProver = Prover.fail) -> AxiomID? {
        guard let prop = parse(prop) else { return nil }
        return assume(prop, prover: prover)
    }
    
    public func define(const : Const, hyps : [Term], body : Term, prover : ContextProver = Prover.fail) -> AxiomID? {
        guard (extend { context in
            return context.kernel.define(const: const, hyps: hyps, body: body) { _, prop in
                return prover.prove(context, prop)
            }
        }) else { return nil }
        return kernel.axioms.count - 1
    }
    
    public func seal(const : Const) -> Bool {
        return extend { context in
            return context.kernel.seal(const: const)
        }
    }

    public func def(_ constant : String, _ definition : String, syntax : [String], priority : ConcreteSyntax.Priority = .None) -> (Const, AxiomID)? {
        guard let body = parse(definition) else { return nil }
        guard let const = declare(constant, syntax: syntax, priority: priority) else { return nil }
        guard let axiom = define(const: const, hyps: [], body: body) else { return nil }
        guard seal(const: const) else { return nil }
        return (const, axiom)
    }

}

extension Context {
    
    public static func root() -> Context {
        let kc = KernelContext.root()
        let context = Context(kc)
        
        func add_syntax(const : Const, syntax : String, priority : Float? = nil) {
            guard context.addSyntax(const: const, syntax: syntax, priority: ConcreteSyntax.Priority.from(priority, default: .Atomic)) else { fatalError() }
        }
        
        add_syntax(const: Const.c_Prop, syntax: "ℙ")
        add_syntax(const: Const.c_eq, syntax: "x = y", priority: ConcreteSyntax.REL_PRIO)
        add_syntax(const: .c_in, syntax: "x : T", priority: ConcreteSyntax.REL_PRIO)
        add_syntax(const: .c_and, syntax: "`p ∧ q", priority: ConcreteSyntax.LOGIC_PRIO + ConcreteSyntax.AND_RPRIO)
        add_syntax(const: .c_imp, syntax: "p ⟶ `q", priority: ConcreteSyntax.LOGIC_PRIO + ConcreteSyntax.IMP_RPRIO)
        add_syntax(const: .c_all, syntax: "∀ x. `P", priority: ConcreteSyntax.BINDER_PRIO)
        add_syntax(const: .c_ex, syntax: "∃ x. `P", priority: ConcreteSyntax.BINDER_PRIO)
        
        return context
    }
}
