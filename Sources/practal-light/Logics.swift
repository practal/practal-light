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
        
        context.declare("(\(c_or). p q)", syntax: "`p ∨ q", priority: S.LOGIC_PRIO + S.OR_RPRIO)

        /*context.axiom("(x = y) : ℙ")
        context.axiom("(p ∧ q) : ℙ")
        context.axiom("(p ⟶ q) : ℙ")
        context.axiom("p ⟶ p : ℙ")
        context.axiom("(p ∨ q) : ℙ")
        context.axiom("(∀ x. P[x]) : ℙ")
        context.axiom("(∃ x. P[x]) : ℙ")*/
        
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
                
        prove_true_is_true(context)
        prove_subst(context)
        
        return context
    }
    
    private static func prove_true_is_true(_ context : Context) {
        let true_def = context.trivial("⊤ = (∀ x. x = x)")!
        let true_sym = context.symmetric(true_def)!
        let eq_subst = context.trivial("x = y ⟶ P[x] ⟶ P[y]")!
        let all = context.all("x", thm: context.trivial("x = x")!)!
        let true_is_true = context.apply(true_sym, all, goal: "⊤", to: eq_subst)!
        context.store(thm: true_is_true)
        /*let all_is_in_Prop = context.trivial("(∀ x. x = x) : ℙ")!
        let true_is_in_Prop = context.apply(true_sym, all_is_in_Prop, goal: "⊤ : ℙ", to: eq_subst)!
        context.store(thm: true_is_in_Prop)*/
    }
    
    private static func prove_subst(_ context : Context) {
        prove_subst1(context)
        prove_subst2(context)
    }
            
    private static func prove_subst1(_ context : Context) {
        let c = context.spawn()
        c.fix("x")
        c.fix("y")
        c.declare("(P. u)", syntax: "P[u]")
        let xy = c.assume("x = y")!
        let Py = c.assume("P[y]")!
        let yx = c.symmetric(xy)!
        let eq_subst = c.trivial("y = x ⟶ P[y] ⟶ P[x]")!
        let th = c.apply(yx, Py, goal: "P[x]", to: eq_subst)!
        let lifted = context.lift(th, from: c)!
        context.store(thm: lifted)
    }
    
    private static func prove_subst2(_ context : Context) {
        let c = context.spawn()
        c.fix("x")
        c.fix("y")
        c.declare("(A. u)", syntax: "A[u]")
        let xy = c.assume("x = y")!
        let eq_subst = c.trivial("x = y ⟶ A[x] = A[x] ⟶ A[x] = A[y]")!
        let Ax_refl = c.trivial("A[x] = A[x]")!
        let th = c.apply(xy, Ax_refl, goal: "A[x] = A[y]", to: eq_subst)!
        let lifted = context.lift(th, from: c)!
        context.store(thm: lifted)
    }
            
    public static let c_false = Const.mkC("false")
    public static let c_not = Const.mkC("not")

    public static func intuitionisticLogic() -> Context {
        let context = minimalLogic()
        
        context.declare("(\(c_false).)", syntax: "⊥")
        
        context.def("(\(c_not). p)", "p ⟶ ⊥", syntax: "¬ `p", priority: S.LOGIC_PRIO + S.NOT_RPRIO)
        
        context.axiom("⊥ ⟶ p")
        
        return context
    }
    
    public static let c_choose = Const.mkC("choose")
    public static let c_if = Const.mkC("if")

    public static func classicalLogic() -> Context {
        let context = intuitionisticLogic()
        
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
