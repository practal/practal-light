    import XCTest
    @testable import practal_light

    final class practal_lightTests: XCTestCase {
        
        func v(_ s : String) -> Var {
            return Id(s)!
        }
        
        func c(_ s : String) -> Const {
            return Id(s)!
        }
        
        func testParser() {
            let parser = PractalExprParser()
            func e(_ expr : String) -> Term {
                let terms = parser.parse(expr: expr)
                XCTAssertEqual(terms.count, 1)
                return terms.first!
            }
            let terms = parser.parse(expr: "(eq. x[y] (eq.u))")
            print("terms = \(terms)")
            let u = e("u")
            let xy = e("x[y]")
            let equ = e("(eq. u)")
            let eq = e("(eq.)")
            XCTAssertEqual(u, Term.variable(v("u"), params: []))
            XCTAssertEqual(xy, Term.variable(v("x"), params: [.variable(v("y"), params: [])]))
            XCTAssertEqual(equ, Term.constant(c("eq"), binders: [], params: [u]))
            XCTAssertEqual(eq, Term.constant(c("eq"), binders: [], params: []))
            let t1 : Term = .constant(c("eq"), binders: [], params: [xy, equ])
            XCTAssertEqual(terms, Set([t1]))
        }
        
        func testCSS() {
            let parser = PractalExprParser()
            let css = parser.parse(css: " ∀ x : Type. B -->   ye:d ")
            XCTAssertEqual(css, ConcreteSyntax(fragments: [.Text("∀"), .Space, .Var(v("x"), raised: true), .Space, .Text(":"), .Space, .Var(v("Type"), raised: true), .Text("."), .Space,
                                                           .Var(v("B"), raised: true), .Space, .Text("-->"), .Space, .Var(v("ye"), raised: true), .Text(":"), .Var(v("d"), raised: true)], priority: nil))
            let selected = css!.selectVars { x in x == v("x") || x == v("B") || x == v("d") }
            print("selected = \(selected)")
            XCTAssertEqual(selected, ConcreteSyntax(fragments: [.Text("∀"), .Space, .Var(v("x"), raised: true), .Space, .Text(":"), .Space, .Keyword("Type"), .Text("."), .Space,
                                                                .Var(v("B"), raised: true), .Space, .Text("-->"), .Space, .Keyword("ye"), .Text(":"), .Var(v("d"), raised: true)], priority: nil))
            let eqAB = parser.parse(css: "A = B")
            XCTAssertEqual(eqAB, ConcreteSyntax(fragments: [.Var(v("A"), raised: true), .Space, .Text("="), .Space, .Var(v("B"), raised: true)], priority: nil))
        }
        
        func testTheory() {
            let parser = PractalExprParser()
            func e(_ expr : String) -> Term {
                let terms = parser.parse(expr: expr)
                XCTAssertEqual(terms.count, 1)
                if terms.count != 1 {
                    print("expr = \(expr)")
                }
                return terms.first!
            }
            let theory = Theory()
            theory.introduce("(eq. A B)", syntax: "A = B")
            let t = theory.parse("(u = (v = w))")
            print("t = \(t)")
            XCTAssertEqual(t, e("(eq. u (eq. v w))"))
            print("pretty = '\(theory.pretty(t))'")
            XCTAssertEqual(theory.pretty(t), "u = (v = w)")
            theory.introduce("(abs x. T B[x])", syntax: "λ x : T. B")
            let lam = theory.parse("λ x : y. z")
            XCTAssertEqual(lam, e("(abs x. y z)"))
            let f = theory.parse("λ x : x. u")
            print("f = \(f)")
            XCTAssertEqual(theory.checkWellformedness(f), [v("x") : 0, v("u") : 0])
            let g = theory.parse("λ x : P[x]. u")
            print("g = \(g)")
            XCTAssertEqual(theory.checkWellformedness(g), [v("x"): 0, v("P"): 1, v("u"): 0])
            let h = theory.parse("λ x : x. P[x]")
            XCTAssertEqual(theory.checkWellformedness(h), [v("x") : 0, v("P") : 1])
        }
        
        func testPracticalTypes() {
            let BINDER_PRIO : Float = 10
            let LOGIC_PRIO : Float = 20
            let REL_PRIO : Float = 30
            let TYPE_PRIO : Float = 40
            //let ARITH_PRIO : Float = 50
            let APP_PRIO : Float = 60
            
            let IMP_RPRIO : Float = 0.1
            let OR_RPRIO : Float = 0.2
            let AND_RPRIO : Float = 0.3
            let NOT_RPRIO : Float = 0.4
            
            let UNION_RPRIO : Float = 0.1
            let FUN_RPRIO : Float = 0.2
            let TYPE_RPRIO : Float = 0.3
                        
            let theory = Theory()
            
            // Mock functions for simulating theory development
            
            func show(_ expr : String) {
                let t = theory.parse(expr)
                XCTAssertNotNil(theory.checkWellformedness(t))
                print("pretty: \(theory.pretty(t)), raw: \(t)")
            }
            
            func introduce(_ expr : String, syntax : String, priority : Float? = nil) {
                theory.introduce(expr, syntax: syntax, priority: priority)
                let t = theory.parse(expr)
                XCTAssertNotNil(theory.checkWellformedness(t))
                print("introduce: \(theory.pretty(t))")
            }
            
            func theorem(_ expr : String) {
                let t = theory.parse(expr)
                XCTAssertNotNil(theory.checkWellformedness(t))
                print("theorem: \(theory.pretty(t))")
            }
            
            func axiom(_ expr : String) {
                let t = theory.parse(expr)
                XCTAssertNotNil(theory.checkWellformedness(t))
                print("axiom: ⊢ \(theory.pretty(t))")
            }
            
            func define(_ abstractSyntax : String, _ definition : String, syntax : String, priority : Float? = nil) {
                let const = theory.define(abstractSyntax, definition, syntax: syntax, priority: priority)
                let t = theory.parse(abstractSyntax)
                print("\(const): ⊢ \(theory.pretty(t)) ≝ \(definition)")
            }
            
            // Theory Development
            
            introduce("(eq. A B)", syntax: "A = B", priority: REL_PRIO)
            
            introduce("(abs x. T B[x])", syntax: "λ x : T. `B", priority: BINDER_PRIO)
            introduce("(app. A B)", syntax: "`A B", priority: APP_PRIO)
            introduce("(in. A T)", syntax: "A : T", priority: REL_PRIO)
            
            introduce("(all x. P[x])", syntax: "∀ x. `P", priority: BINDER_PRIO)
            introduce("(choose x. T P[x])", syntax: "ε x : T. `P", priority: BINDER_PRIO)
            introduce("(imp. A B)", syntax: "A ⟶ `B", priority: LOGIC_PRIO + IMP_RPRIO)
            introduce("(false.)", syntax: "⊥")
            
            introduce("(Prop.)", syntax: "ℙ")
            introduce("(Fun. U V)", syntax: "U → `V", priority: TYPE_PRIO + FUN_RPRIO)
            introduce("(Pred x. T P[x])", syntax: "{ x : T | P }")
            introduce("(Type. i)", syntax: "Type i", priority: TYPE_PRIO + TYPE_RPRIO)
            introduce("(Union i. I T[i])", syntax: "⋃ i : I. `T", priority: TYPE_PRIO + UNION_RPRIO)

            introduce("(Nat.)", syntax: "ℕ")
            introduce("(Nat-zero.)", syntax: "0")
            introduce("(Nat-succ.)", syntax: "succ")

            XCTAssertEqual(theory.parse("Type i → V"), theory.parse("(Type i) → V"))
            XCTAssertEqual(theory.parse("A B C"), theory.parse("(A B) C"))
            XCTAssertTrue(theory.parseAll("A = B = C").isEmpty)

            define("(not. P)", "P ⟶ ⊥", syntax: "¬`P", priority: LOGIC_PRIO + NOT_RPRIO)
            define("(true.)", "¬ ⊥", syntax: "⊤")
            define("(or. P Q)", "¬P ⟶ Q", syntax: "`P ∨ Q", priority: LOGIC_PRIO + OR_RPRIO)
            define("(and. P Q)", "¬(¬P ∨ ¬Q)", syntax: "`P ∧ Q", priority: LOGIC_PRIO + AND_RPRIO)
            define("(equiv. P Q)", "(P ⟶ Q) ∧ (Q ⟶ P)", syntax: "P ≡ Q", priority: REL_PRIO)
            define("(neq. P Q)", "¬(P = Q)", syntax: "P ≠ Q", priority: REL_PRIO)
            define("(ex x. P[x])", "¬(∀ x. ¬P[x])", syntax: "∃ x. `P", priority: BINDER_PRIO)
            define("(all-in x. T P[x])", "∀ x. x : T ⟶ P[x]", syntax: "∀ x : T. `P", priority: BINDER_PRIO)
            define("(ex-in x. T P[x])", "∃ x. x : T ∧ P[x]", syntax: "∃ x : T. `P", priority: BINDER_PRIO)
            define("(sub-type. U V)", "∀ u : U. u : V", syntax: "U ⊆ V", priority: REL_PRIO)
                        
            axiom("a = a")
            axiom("(a = b) : ℙ")
            axiom("∀ p : ℙ. p = ⊥ ∨ p = ⊤")
            axiom("⊤ ≠ ⊥")
            
            define("(Empty.)", "{ p : ℙ | ⊥ }", syntax: "∅")
            
            axiom("f : A → B ⟶ (∀ a : A. f x : B)")
            axiom("∀ f : A → B. ∀ g : C → D. (f = g) = (A = C ∧ (∀ x : A. f x = g x))")
            theorem("(A → B ⊆ C → D) = (A = C ∧ (A = ∅ ∨ B ⊆ D))")
            
            show("A ≠ ∅")
            show("(A → ∅) = ∅")
            show("(∅ → B) = (∅ → ∅)")
            
            define("(Nil.)", "∅ → ∅", syntax: "Nil")
            define("(nil.)", "λ x : ∅. ⊥", syntax: "nil")
            
            show("nil")
            
            axiom("f : A → B ⟶ ¬ (x : A) ⟶ f x = nil")
            
            define("(is-Fun. f)", "∃ U. ∃ V. f : U → V", syntax: "f : Fun", priority: REL_PRIO)
            
            show("f : Fun")
            
            define("(all-fun f. P[f])", "∀ f. f : Fun ⟶ P[f]", syntax: "∀ f : Fun. `P", priority: BINDER_PRIO)
            define("(ex-fun f. P[f])", "∃ f. f : Fun ⟶ P[f]", syntax: "∃ f : Fun. `P", priority: BINDER_PRIO)
            
            axiom("¬(A : Fun) ⟶ A B = nil")
            
            show("¬(A : Fun) ⟶ A B = nil")
            
            define("(defined. x)", "x ≠ nil", syntax: "x↓", priority: REL_PRIO)
            define("(undefined. x)", "x = nil", syntax: "x↑", priority: REL_PRIO)
            define("(defined-eq. x y)", "(x↓ ∨ y↓) ∧ x = y", syntax: "x =↓ y", priority: REL_PRIO)
            define("(undefined-eq. x y)", "x↑ ∨ y↑ ∨ x = y", syntax: "x =↑ y", priority: REL_PRIO)
            
            show("{ a : A | P a }")
            
            axiom("(a : { a : A | P a }) = (a : A ∧ P a)")
            
            show("{ T : Type i | ¬(T : T) }")
            
            show("succ succ n")
            show("Type Type i")
            show("Type succ 0")
            show("f succ 0")
            
            axiom("0 : ℕ")
            axiom("succ : ℕ → ℕ")
            axiom("succ n ≠ 0")
            axiom("succ(m) =↓ succ(n) ⟶ m = n")
            axiom("0 : N ⟶ (∀ n : N. succ n : N) ⟶ ℕ ⊆ N")
            
            define("(Type-0.)", "Type 0", syntax: "𝕋")
            axiom("ℙ : 𝕋")
            axiom("ℕ : 𝕋")
            axiom("A : Type i ⟶ B : Type i ⟶ A → B : Type i")
            axiom("A : Type i ⟶ P : A → ℙ ⟶ { a : A | P a } : Type i")
            axiom("i : ℕ ⟶ Type i : Type (succ i)")
            axiom("i : ℕ ⟶ Type i ⊆ Type (succ i)")
            
        }
    }
