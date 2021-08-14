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

    public static let c_false = Const.mkC("false")
    public static let c_not = Const.mkC("not")
    
    public static let c_choose = Const.mkC("choose")

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
        context.axiom("x = y ⟶ A[x] = A[y]")

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

        return context
    }
        
    public static func intuitionisticLogic() -> Context {
        let context = minimalLogic()
        
        context.declare("(\(c_false).)", syntax: "⊥")
        
        context.def("(\(c_not). p)", "p ⟶ ⊥", syntax: "¬ `p", priority: S.LOGIC_PRIO + S.NOT_RPRIO)
        
        context.axiom("p : ℙ ⟶ ⊥ ⟶ p")
        
        return context
    }
    
    public static func classicalLogic() -> Context {
        let context = intuitionisticLogic()
        
        context.axiom("¬ ¬ p ⟶ p")
        
        context.declare("(\(c_choose) x. P[x])", syntax: "ε x. `P", priority: S.BINDER_PRIO)
        context.axiom("(∃ x. P[x]) ⟶ P[ε x. P[x]]")
        
        return context
    }
    
    public static func practicalTypes() -> Context {
        fatalError()
    }
    
}
