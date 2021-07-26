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
            let terms = parser.parse(expr: "eq. x[y] eq.u")
            print("terms = \(terms)")
            let u = e("u")
            let xy = e("x[y]")
            let equ = e("eq. u")
            let eq = e("eq.")
            XCTAssertEqual(u, Term.variable(v("u"), dependencies: []))
            XCTAssertEqual(xy, Term.variable(v("x"), dependencies: [v("y")]))
            XCTAssertEqual(equ, Term.constant(c("eq"), binders: [], params: [u]))
            XCTAssertEqual(eq, Term.constant(c("eq"), binders: [], params: []))
            let t1 : Term = .constant(c("eq"), binders: [], params: [xy, equ])
            let t2 : Term = .constant(c("eq"), binders: [], params: [xy, eq, u])
            XCTAssertEqual(terms, Set([t1, t2]))
        }
        
        func testCSS() {
            let parser = PractalExprParser()
            let css = parser.parse(css: " ∀ x : Type. B -->   ye:d ")
            XCTAssertEqual(css, ConcreteSyntax(fragments: [.Text("∀"), .Space, .Var(v("x")), .Text(":"), .Space, .Var(v("Type")), .Text("."), .Space,
                                                           .Var(v("B")), .Text("-->"), .Space, .Var(v("ye")), .Text(":"), .Var(v("d"))]))
            let selected = css!.selectVars { x in x == v("x") || x == v("B") || x == v("d") }
            print("selected = \(selected)")
            XCTAssertEqual(selected, ConcreteSyntax(fragments: [.Text("∀"), .Space, .Var(v("x")), .Text(":"), .Space, .Text("Type"), .Text("."), .Space,
                                                                .Var(v("B")), .Text("-->"), .Space, .Text("ye"), .Text(":"), .Var(v("d"))]))
        }
    }
