//
//  Logics.swift
//  
//
//  Created by Steven Obua on 14/08/2021.
//

import Foundation

public struct Logics {
    
    public static let c_or = Const.mkC("or")
    
    public static func minimalLogic() -> Context {
        let context = Context.root()
        print(context.kernel.description)
        context.declare("(\(c_or). p q)", syntax: "`p ∨ q", priority: ConcreteSyntax.LOGIC_PRIO + ConcreteSyntax.OR_RPRIO)
        
        func axiom(_ prop : String) {
            guard context.assume(prop, prover: Prover.debug(Prover.byAxioms)) != nil else { fatalError() }
        }
        
        axiom("(x = y) : ℙ")
        axiom("(p ∧ q) : ℙ")
        axiom("(p ⟶ q) : ℙ")
        axiom("(p ∨ q) : ℙ")
        axiom("(∀ x. P[x]) : ℙ")
        axiom("(∃ x. P[x]) : ℙ")
        
        axiom("x = x")
        axiom("x = y ⟶ y = x")
        axiom("x = y ⟶ y = z ⟶ x = z")

        axiom("p ∧ q ⟶ p")
        axiom("p ∧ q ⟶ q")
        axiom("p ⟶ q ⟶ p ∧ q")
        
        axiom("p ⟶ p ∨ q")
        axiom("q ⟶ p ∨ q")
        axiom("p ∨ q ⟶ (p ⟶ r) ⟶ (q ⟶ r) ⟶ r")

        axiom("(∀ x. P[x]) ⟶ P[t]")
        axiom("P[t] ⟶ (∃ x. P[x])")

        return context
    }
        
    public static func intuitionisticLogic() -> Context {
        fatalError()
    }
    
    public static func classicalLogic() -> Context {
        fatalError()
    }
    
    public static func practicalTypes() -> Context {
        fatalError()
    }
    
}
