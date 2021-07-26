    import XCTest
    @testable import practal_light

    final class practal_lightTests: XCTestCase {
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
            XCTAssertEqual(u, Term.variable("u", dependencies: []))
            XCTAssertEqual(xy, Term.variable("x", dependencies: ["y"]))
            XCTAssertEqual(equ, Term.constant("eq", binders: [], params: [u]))
            XCTAssertEqual(eq, Term.constant("eq", binders: [], params: []))
            let t1 : Term = .constant("eq", binders: [], params: [xy, equ])
            let t2 : Term = .constant("eq", binders: [], params: [xy, eq, u])
            XCTAssertEqual(terms, Set([t1, t2]))
        }
    }
