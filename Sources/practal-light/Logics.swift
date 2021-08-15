//
//  Logics.swift
//  
//
//  Created by Steven Obua on 14/08/2021.
//

import Foundation

public struct Logics {
    private typealias S = ConcreteSyntax
    
    public static let c_or = Const.mkC("or")
    public static let c_true = Const.mkC("true")
    public static let c_equiv = Const.mkC("equiv")
    
    public static func minimalLogic() -> Context {
        let context = Context.root()
        print(context.kernel.description)
        
        context.declare("(\(c_or). p q)", syntax: "`p ∨ q", priority: S.LOGIC_PRIO + S.OR_RPRIO)

        context.axiom("(x = y) : ℙ")
        context.axiom("(p ∧ q) : ℙ")
        context.axiom("(p ⟶ q) : ℙ")
        context.axiom("p ⟶ p : ℙ")
        context.axiom("(p ∨ q) : ℙ")
        context.axiom("(∀ x. P[x]) : ℙ")
        context.axiom("(∃ x. P[x]) : ℙ")
        
        context.axiom("x = x")
        context.axiom("x = y ⟶ y = x")
        context.axiom("x = y ⟶ y = z ⟶ x = z")
        context.axiom("x = y ⟶ P[x] ⟶ P[y]")

        context.axiom("p ∧ q ⟶ p")
        context.axiom("p ∧ q ⟶ q")
        context.axiom("p ⟶ q ⟶ p ∧ q")
        
        context.axiom("p ⟶ p ∨ q")
        context.axiom("q ⟶ p ∨ q")
        context.axiom("p ∨ q ⟶ (p ⟶ r) ⟶ (q ⟶ r) ⟶ r")

        context.axiom("(∀ x. P[x]) ⟶ P[t]")
        context.axiom("P[t] ⟶ (∃ x. P[x])")
        
        context.def("(\(c_true).)", "∀ x. x = x", syntax: "⊤")
        context.def("(\(c_equiv). p q)", "(p ⟶ q) ∧ (q ⟶ p)", syntax: "p ⟷ q", priority: S.LOGIC_PRIO + S.EQUIV_RPRIO)
        
        //context.trivial("(⊤ = ∀ x. x = x) ⟶  ")
        
        let th = context.all("x", thm: context.trivial("x = x"))
        print("th = \(th)")

        return context
    }
        
    public static let c_false = Const.mkC("false")
    public static let c_not = Const.mkC("not")

    public static func intuitionisticLogic() -> Context {
        let context = minimalLogic()
        
        context.declare("(\(c_false).)", syntax: "⊥")
        
        context.def("(\(c_not). p)", "p ⟶ ⊥", syntax: "¬ `p", priority: S.LOGIC_PRIO + S.NOT_RPRIO)
        
        context.axiom("p : ℙ ⟶ ⊥ ⟶ p")
        
        return context
    }
    
    public static let c_choose = Const.mkC("choose")
    public static let c_if = Const.mkC("if")

    public static func classicalLogic() -> Context {
        let context = intuitionisticLogic()
        print(context.description)
        
        context.axiom("¬ ¬ p ⟶ p")
        
        context.declare("(\(c_choose) x. P[x])", syntax: "ε x. `P", priority: S.BINDER_PRIO)
        context.axiom("(∃ x. P[x]) ⟶ P[ε x. P[x]]")
        
        context.def("(\(c_if). p A B)", "ε x. (p ⟶ x = A) ∧ (¬ p ⟶ x = B)", syntax: "if p then A else B", priority: S.CONTROL_PRIO)
        
        return context
    }
    
    public static let c_is_Type = Const.mkC("is-Type")
    public static let c_Empty = Const.mkC("Empty")

    public static func practicalTypes() -> Context {
        let context = classicalLogic()
        
        context.declare("(\(c_Empty).)", syntax: "∅")
        context.axiom("¬(x : ∅)")
        
        context.def("(\(c_is_Type). T)", "T = ∅ ∨ (∃ x. x : T)", syntax: "T : 𝕋")
        
        return context
    }
    
}
