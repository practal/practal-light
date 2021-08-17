    import XCTest
    @testable import practal_light

    final class practal_lightTests: XCTestCase {
        
        func v(_ s : String) -> Var {
            return Var(s)!
        }
        
        func c(_ s : String) -> Const {
            return Const(s)!
        }

        func testConst() {
            let parser = PractalExprParser()
            let const = c("eq.u")
            XCTAssertEqual(const.namespace.components.count, 1)
            XCTAssertEqual(parser.parse(expr: "(eq.u)"), [])
            XCTAssertEqual(parser.parse(expr: "(eq.u.)"), [.constant(const, binders: [], params: [])])
            XCTAssertEqual(parser.parse(expr: "(eq. u.)"), [])
            let v : Term = .variable(v("u"), params: [])
            XCTAssertEqual(parser.parse(expr: "(eq. u)"), [.constant(c("eq"), binders: [], params: [v])])
        }
        
        func testVar() {
            let parser = PractalExprParser()
            func get(_ w : String) -> Var {
                let terms = parser.parse(expr: w)
                XCTAssertEqual(terms.count, 1)
                let t = terms.first!
                switch t {
                case let .variable(v, params: []):
                    return v
                default:
                    XCTFail()
                    fatalError()
                }
            }
            let w0 = get("w")
            let w1 = get("w\(Var.PRIME)")
            let w2 = get("w\(Var.PRIME)\(Var.PRIME)")
            let v0 = v("w")
            let v1 = v("w\(Var.PRIME)")
            let v2 = v("w\(Var.PRIME)\(Var.PRIME)")
            let id = Id("w")!
            XCTAssertEqual(w0, Var(name: id, primes: 0))
            XCTAssertEqual(w1, Var(name: id, primes: 1))
            XCTAssertEqual(w2, Var(name: id, primes: 2))
            XCTAssertEqual(v0, Var(name: id, primes: 0))
            XCTAssertEqual(v1, Var(name: id, primes: 1))
            XCTAssertEqual(v2, Var(name: id, primes: 2))
        }
        
        func testParser() {
            let parser = PractalExprParser()
            func e(_ expr : String) -> Term {
                let terms = parser.parse(expr: expr)
                XCTAssertEqual(terms.count, 1)
                return terms.first!
            }
            let terms = parser.parse(expr: "(eq. x[y] (eq. u))")
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
                                                           .Var(v("B"), raised: true), .Space, .Text("-->"), .Space, .Var(v("ye"), raised: true), .Text(":"), .Var(v("d"), raised: true)], priority: .None))
            let selected = css!.selectVars { x in x == v("x") || x == v("B") || x == v("d") }
            print("selected = \(selected)")
            XCTAssertEqual(selected, ConcreteSyntax(fragments: [.Text("∀"), .Space, .Var(v("x"), raised: true), .Space, .Text(":"), .Space, .Keyword("Type"), .Text("."), .Space,
                                                                .Var(v("B"), raised: true), .Space, .Text("-->"), .Space, .Keyword("ye"), .Text(":"), .Var(v("d"), raised: true)], priority: .None))
            let eqAB = parser.parse(css: "A = B")
            XCTAssertEqual(eqAB, ConcreteSyntax(fragments: [.Var(v("A"), raised: true), .Space, .Text("="), .Space, .Var(v("B"), raised: true)], priority: .None))
        }
        
        /*func testPretty() {
            let theory = Theory()
            theory.introduce("(eq. A B)", syntax: "A = B")
            let t = theory.parse("(u = (v = w))")
            print("pretty = \(theory.pretty(t))")
        }*/
        
        /*func testTheory() {
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
        }*/
        
        /*func testPracticalTypes() {
            let CONTROL_PRIO : Float = 0
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
            let BINARY_UNION_RPRIO : Float = 0.3
            let BINARY_INTERSECTION_RPRIO : Float = 0.4
            let TYPE_RPRIO : Float = 0.5
                        
            let theory = Theory()
            
            // Mock functions for simulating theory development
            
            func show(_ expr : String) {
                let t = theory.parse(expr)
                XCTAssertNotNil(theory.checkWellformedness(t))
                print("pretty: \(theory.pretty(t)), raw: \(t)")
            }
            
            func introduce(_ expr : String, syntax : String, priority : Float? = nil) {
                theory.introduce(expr, syntax: syntax, priority: ConcreteSyntax.Priority.from(priority, default: .Atomic))
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
                let const = theory.define(abstractSyntax, definition, syntax: syntax, priority: ConcreteSyntax.Priority.from(priority, default: .Atomic))
                let t = theory.parse(abstractSyntax)
                print("\(const): ⊢ \(theory.pretty(t)) ≝ \(definition)")
            }
            
            // Theory Development
            
                        
            introduce("(eq. A B)", syntax: "A = B", priority: REL_PRIO)
            
            introduce("(abs x. T B[x])", syntax: "λ x : T. `B", priority: BINDER_PRIO)
            introduce("(app. A B)", syntax: "`A B", priority: APP_PRIO)
            introduce("(in. A T)", syntax: "A : T", priority: REL_PRIO)
            
            introduce("(all x. P[x])", syntax: "∀ x. `P", priority: BINDER_PRIO)
            introduce("(choose x. P[x])", syntax: "ε x. `P", priority: BINDER_PRIO)
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
            define("(is-Type. T)", "∃ i. T : Type i", syntax: "T : Type", priority: REL_PRIO)
            define("(if-then-else. p A B)", "ε x. (p ⟶ x = A) ∧ (¬ p ⟶ x = B)", syntax: "if p then A else B", priority: CONTROL_PRIO)
            define("(sub-type. U V)", "U : Type ∧ V : Type ∧ (∀ u : U. u : V)", syntax: "U ⊆ V", priority: REL_PRIO)
            define("(Singleton. x)", "{ y : (ε T. x : T) | x = y }", syntax: "{ x }")
            
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
            define("(ex-fun f. P[f])", "∃ f. f : Fun ∧ P[f]", syntax: "∃ f : Fun. `P", priority: BINDER_PRIO)
            
            axiom("¬(A : Fun) ⟶ A B = nil")
            
            show("¬(A : Fun) ⟶ A B = nil")
            
            define("(defined. x)", "x ≠ nil", syntax: "x↓", priority: REL_PRIO)
            define("(undefined. x)", "x = nil", syntax: "x↑", priority: REL_PRIO)
            define("(defined-eq. x y)", "(x↓ ∨ y↓) ∧ x = y", syntax: "x =↓ y", priority: REL_PRIO)
            define("(undefined-eq. x y)", "x↑ ∨ y↑ ∨ x = y", syntax: "x =↑ y", priority: REL_PRIO)
            
            axiom("(∃ x. P[x]) ⟶ P[ε x. P[x]]")
            axiom("¬(∃ x. P[x]) ⟶ (ε x. P[x]) = nil")
            
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
            
            show("t : Type")
            
            define("(all-type T. P[T])", "∀ T. T : Type ⟶ P[T]", syntax: "∀ T : Type. `P", priority: BINDER_PRIO)
            define("(ex-type T. P[T])", "∃ T. T : Type ∧ P[T]", syntax: "∃ T : Type. `P", priority: BINDER_PRIO)
            
            axiom("(∀ a : A. T[a] : Type i) ⟶ (x : ⋃ a : A. T[a]) = (∃ a : A. x : T[a])")
            axiom("(∀ a : A. T[a] : Type i) ⟶ (⋃ a : A. T[a]) : Type i")
            axiom("¬(∃ i : ℕ. ∀ a : A. T[a] : Type i) ⟶ (⋃ a : A. T[a]) = nil")
            
            show("⋃ T : 𝕋. T")
            
            define("(Intersection i. I T[i])", "{ x : ⋃ i : I. T[i] | ∀ i : I. x : T[i] }", syntax: "⋂ i : I. `T", priority: TYPE_PRIO + UNION_RPRIO)
            
            define("(Binary-Union. A B)", "⋃ p : ℙ. (if p then A else B)", syntax: "`A ∪ B", priority: TYPE_PRIO + BINARY_UNION_RPRIO)
            define("(Binary-Intersection. A B)", "⋂ p : ℙ. (if p then A else B)", syntax: "`A ∩ B", priority: TYPE_PRIO + BINARY_INTERSECTION_RPRIO)
            
            show("A ∩ B ∪ C")
            show("A ∪ B ∩ C")
            
            axiom("¬ (x : Type) ⟶ (∃ T : 𝕋. x : T)")
            show("{ x } = { y : T | y = x }")
            
            axiom("T → (⋃ x : T. {B[x]}) ↓ ⟶ (λ x : T. B[x]) : T → (⋃ x : T. {B[x]})")
            axiom("T → (⋃ x : T. {B[x]}) ↑ ⟶ (λ x : T. B[x]) = nil")
            axiom("T → (⋃ x : T. {B[x]}) ↓ ⟶ x : T ⟶ (λ x : T. B[x]) x = B[x]")
            
            // for now, do a simple definition
            define("(Pair. U V)", "{ f : ℙ → U ∪ V | f ⊥ : U ∧ f ⊤ : V }", syntax: "U ⨯ `V")
            introduce("(fst. p)", syntax: "fst p", priority: APP_PRIO)
            introduce("(snd. p)", syntax: "snd p", priority: APP_PRIO)

            define("(D-Fun a. A B[a])", "{ f : A → (⋃ a : A. B[a]) | ∀ a : A. f a : B[a] }", syntax: "[a : A] → `B", priority: TYPE_PRIO + FUN_RPRIO)
            define("(D-Pair a. A B[a])", "{ p : A ⨯ (⋃ a : A. B[a]) | snd p : B[fst p] }", syntax: "[a : A] ⨯ `B", priority: TYPE_PRIO + FUN_RPRIO)
            
            axiom("ℙ ∩ ℕ = ∅")
            axiom("ℙ ∩ (A → B) =↑ ∅")
            axiom("ℙ ∩ (A ⨯ B) =↑ ∅")
            axiom("ℙ ∩ Type i =↑ ∅")
            axiom("ℕ ∩ (A → B) =↑ ∅")
            axiom("ℕ ∩ (A ⨯ B) =↑ ∅")
            axiom("ℕ ∩ Type i =↑ ∅")
            axiom("(A → B) ∩ (A ⨯ B) =↑ ∅")
            axiom("ℕ ∩ Type i =↑ ∅")
            axiom("(A → B) ∩ (A ⨯ B) =↑ ∅")
            axiom("(A → B) ∩ Type i =↑ ∅")
            axiom("(A ⨯ B) ∩ Type i =↑ ∅")
            axiom("¬ (A : Type) ∨ ¬ (B : Type) ⟶ (A → B) = nil")
            axiom("¬ (A : Type) ∨ ¬ (B : Type) ⟶ (A ⨯ B) = nil")
            axiom("¬ (i : ℕ) ⟶ Type i = nil")
            axiom("¬ (T : Type) ⟶ (x : T) = nil")
            axiom("¬ (T : Type) ⟶ { x : T | P[x] } = nil")
            axiom("¬ (P : ℙ ∪ Nil) ⟶ (¬ P)↑")
            axiom("¬ (P : ℙ ∪ Nil) ⟶ (P ⟶ Q)↑")
            axiom("¬ (Q : ℙ ∪ Nil) ⟶ (P ⟶ Q)↑")
            axiom("¬ ⊥")
            axiom("¬ nil")
            axiom("(¬ ⊤) = ⊥")
            axiom("P : ℙ ∪ Nil ⟶ nil ⟶ A")
            axiom("P : ℙ ∪ Nil ⟶ ⊥ ⟶ A")
            axiom("⊤ ⟶ ⊤")
            axiom("(⊤ ⟶ ⊥) = ⊥")
            axiom("(⊤ ⟶ nil) = ⊥")
        }*/
        
        func testContext() {
            let context = Context.root()
            print(context.kernel.description)

            func show(_ expr : String) {
                let t = context.parse(expr)!
                XCTAssertTrue(context.isWellformed(t))
                print("pretty: \(context.pretty(t)), raw: \(t)")
            }
             
            show("ℙ")
            show("x = ℙ")
            show("t")
            show("t : ℙ")
            show("a ∧ t ∧ x")
            show("r ∧ d ⟶ a ∧ t ∧ x ⟶ i ∧ j")
            show("∀ x. ∃ y. x = y")

        }
        
        func testMatching() {
            let context = Context.root()
            let ax = context.parse("x = y ⟶ P[x] ⟶ P[y]")!
            print("-----------------")
            XCTAssertEqual(context.match(pattern: ax, instance: ax).count, 1)
            let ax2 = context.parse("x = y ⟶ P[x]")!
            print("-----------------")
            let matches = context.match(pattern: ax2, instance: ax2)
            XCTAssertEqual(matches.count, 2)
            print("number of matches: \(matches.count)")
            for m in matches {
                print("- \(m)")
            }
        }
        
        func testLogics() {
            let context = Logics.minimalLogic()//Logics.practicalTypes()
            print(context.kernel.description)
            
            func show(_ expr : String) {
                let t = context.parse(expr)!
                XCTAssertTrue(context.isWellformed(t))
                print("pretty: \(context.pretty(t)), raw: \(t)")
            }
            
            /*show("ℙ")
            show("x = ℙ")
            show("t")
            show("t : ℙ")
            show("a ∧ ⊥ ∧ x")
            show("r ∧ d ⟶ a ∧ ⊥ ∧ x ⟶ i ∧ j")
            show("∀ x. ∃ y. x = y")*/
        }
        
        func testKernelContext() {
            let kc = KernelContext.root()
            print(kc.description)
        }
        
        func testTm() {
            let parser = PractalExprParser()
            let kc = KernelContext.root()
            let term = parser.parse("(Practal.eq. a (Practal.ex x. (Practal.eq. x T)))")!
            print("term = \(term)")
            let tm = Tm.fromWellformedTerm(kc, term: term)!
            print("tm = \(tm)")
            var subst = TmSubstitution()
            subst[Var("T")!] = TmWithHoles(holes: 0, .bound(1))
            print("subst = \(subst.apply(tm)!)")
        }
    }
