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
            XCTAssertEqual(u, Term.variable(v("u"), dependencies: []))
            XCTAssertEqual(xy, Term.variable(v("x"), dependencies: [v("y")]))
            XCTAssertEqual(equ, Term.constant(c("eq"), binders: [], params: [u]))
            XCTAssertEqual(eq, Term.constant(c("eq"), binders: [], params: []))
            let t1 : Term = .constant(c("eq"), binders: [], params: [xy, equ])
            XCTAssertEqual(terms, Set([t1]))
        }
        
        func testCSS() {
            let parser = PractalExprParser()
            let css = parser.parse(css: " ∀ x : Type. B -->   ye:d ")
            XCTAssertEqual(css, ConcreteSyntax(fragments: [.Text("∀"), .Space, .Var(v("x")), .Space, .Text(":"), .Space, .Var(v("Type")), .Text("."), .Space,
                                                           .Var(v("B")), .Space, .Text("-->"), .Space, .Var(v("ye")), .Text(":"), .Var(v("d"))], priority: nil))
            let selected = css!.selectVars { x in x == v("x") || x == v("B") || x == v("d") }
            print("selected = \(selected)")
            XCTAssertEqual(selected, ConcreteSyntax(fragments: [.Text("∀"), .Space, .Var(v("x")), .Space, .Text(":"), .Space, .Text("Type"), .Text("."), .Space,
                                                                .Var(v("B")), .Space, .Text("-->"), .Space, .Text("ye"), .Text(":"), .Var(v("d"))], priority: nil))
            let eqAB = parser.parse(css: "A = B")
            XCTAssertEqual(eqAB, ConcreteSyntax(fragments: [.Var(v("A")), .Space, .Text("="), .Space, .Var(v("B"))], priority: nil))
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
            XCTAssertEqual(theory.pretty(t), "(u = (v = w))")
            theory.introduce("(abs x. T B[x])", syntax: "λ x : T. B")
            let lam = theory.parse("λ x : y. z")
            XCTAssertEqual(lam, e("(abs x. y z)"))
            let f = theory.parse("λ x : x. u")
            print("f = \(f)")
            XCTAssertEqual(theory.checkWellformedness(f), [v("x") : 0, v("u") : 0])
            let g = theory.parse("λ x : P[x]. u")
            print("g = \(g)")
            XCTAssertNil(theory.checkWellformedness(g))
            let h = theory.parse("λ x : x. P[x]")
            XCTAssertEqual(theory.checkWellformedness(h), [v("x") : 0, v("P") : 1])
        }
        
        func testPracticalTypes() {
            let BINDER_PRIO : Float = 10
            let REL_PRIO : Float = 15
            let APP_PRIO : Float = 20
            
            let theory = Theory()
            theory.introduce("(eq. A B)", syntax: "A = B", priority: REL_PRIO)
            theory.introduce("(abs x. T B[x])", syntax: "λ x : T. B", priority: BINDER_PRIO)
            theory.introduce("(app. A B)", syntax: "A B", priority: APP_PRIO)
            theory.introduce("(all x. P[x])", syntax: "∀ x. P", priority: BINDER_PRIO)
        }
    }
