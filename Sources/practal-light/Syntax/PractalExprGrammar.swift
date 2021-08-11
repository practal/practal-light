//
//  PractalExprGrammar.swift
//
//  Created by Steven Obua on 24/07/2021.
//

import Foundation
import ParsingKit
import FirstOrderDeepEmbedding

public class PractalExprGrammar : TextGrammar {
    
    typealias N = NONTERMINAL
    typealias T = TERMINAL
    
    @Sym var PractalExpr : N
    @Sym var _Expr : N
    @Sym var _AtomicExpr : N

    @Sym var ExprList : N
    @Sym var ExprCommaList : N

    @Sym var Variable : N
    @Sym var Constant : N
    @Sym var Var : T
    @Sym var Const : T
    @Sym var VarList : N
    @Sym var _VarList1 : N

    @Sym var Id : T
    @Sym var StartIdFragment : T
    @Sym var IdFragment : T
    @Sym var Hyphen : T
    @Sym var Letter : T
    @Sym var Digit : T

    @Sym var _Space : T
    @Sym var _OptSpace : T
    
    @Sym var ConcreteSyntaxSpec : N
    @Sym var _ConcreteSyntaxFragment : N
    @Sym var CSF_Space : T
    @Sym var CSF_Var : T
    @Sym var CSF_RaisedVar : T
    @Sym var CSF_Text : T
    
    private let syntax : Syntax
    
    public init(syntax : Syntax) {
        self.syntax = syntax
        super.init()
    }

    public func addIDRules() {
        add {
            Hyphen.rule {
                const("-")
            }
            
            Letter.rule {
                Char
                %?(Char~.inRange("a", "z") || Char~.inRange("A", "Z"))
            }
            
            Digit.rule {
                Char
                %?(Char~.inRange("0", "9"))
            }

            StartIdFragment.rule {
                Letter
                IdFragment
            }

            IdFragment.rule {
                RepeatGreedy(OrGreedy(Digit, Letter))
            }
            
            Id.rule {
                StartIdFragment
                RepeatGreedy(Seq(Hyphen, IdFragment))
            }
        }
    }
    
    public func addSpaceRules() {
        add {
            _Space.rule {
                Repeat1Greedy(const(" "))
            }
            
            _OptSpace.rule {
                RepeatGreedy(const(" "))
            }
        }
    }
                    
    public func addVariableRules() {
        add {
            Var.rule {
                Id
                RepeatGreedy(const(practal_light.Var.PRIME))
            }
                        
            Variable.rule {
                Var
                const("[")
                ExprCommaList
                const("]")
            }

            Variable.rule {
                Var
            }
        }
    }
    
    public func addListRules() {
        add {
            _VarList1.rule {
                Var
            }
            
            _VarList1.rule {
                _VarList1[1]
                _OptSpace
                Var
            }
            
            VarList.rule {
                _OptSpace[0]
                _VarList1
                _OptSpace[1]
            }
            
            VarList.rule {
                _OptSpace
            }

            ExprList.rule {
                Seq(_AtomicExpr, RepeatGreedy(Seq(_OptSpace, _AtomicExpr)))
            }
            
            ExprList.rule { }

            ExprCommaList.rule {
                Seq(_Expr, RepeatGreedy(Seq(_OptSpace, const(","), _OptSpace, _Expr)))
            }
            
            ExprCommaList.rule {
                _OptSpace
            }
        }
    }
    
    public func addConstantRules() {
        add {
                        
            Const.rule {
                Seq(Id, RepeatGreedy(Seq(const(Namespace.SEPARATOR), Id)))
            }
                                    
            Constant.rule {
                const("(")
                _OptSpace[0]
                Const
                VarList
                const(".")
                _OptSpace[1]
                ExprList
                _OptSpace[2]
                const(")")
            }
        }
    }
    
    public class Priorities {
        
        var prioExprs : [N] = []
        var prioRanks : [Float : Int] = [:]
        var topExpr : N
        var atomicExpr : N
        
        init(_ prios : Set<Float>, grammar : PractalExprGrammar) {
            let priorities = Array(prios).sorted()
            for (rank, p) in priorities.enumerated() {
                prioRanks[p] = rank
                prioExprs.append(grammar.nonterminal(SymbolName("_Expr-with-prio-\(rank)")))
            }
            topExpr = grammar._Expr
            atomicExpr = grammar._AtomicExpr
            var current = topExpr
            for prioExpr in prioExprs + [atomicExpr] {
                grammar.add {
                    current.rule {
                        prioExpr
                    }
                }
                current = prioExpr
            }
        }
                
        func lookup(_ priority : ConcreteSyntax.Priority) -> (parent: N, child: N, raised_child: N) {
            switch priority {
            case .Level(let l): return lookup(l)
            case .None, .Atomic: return lookup(nil)
            }
        }
        
        func lookup(_ priority : Float?) -> (parent: N, child: N, raised_child: N) {
            guard let p = priority else { return (atomicExpr, topExpr, topExpr) }
            let rank = prioRanks[p]!
            let E = prioExprs[rank]
            let E_raised = rank+1 < prioExprs.count ? prioExprs[rank + 1] : atomicExpr
            return (E, E, E_raised)
        }
        
        func debug() {
            print("There are \(prioExprs.count) intermittent priorities:")
            for (i, e) in prioExprs.enumerated() {
                print("\(i+1). \(e)")
            }
        }
        
    }

    func constConcreteRuleBody(abstractSyntax : AbstractSyntax, concreteSyntax : ConcreteSyntax, E : N, E_raised : N) -> RuleBody {
        var elems : [RuleBody] = []
        var i = 0
        var first : Bool = true
        for fragment in concreteSyntax.fragments {
            switch fragment {
            case .Space:
                if !first {
                    elems.append(_OptSpace[i])
                    first = true
                }
            case .Text(let syntax):
                if !first {
                    elems.append(_OptSpace[i])
                }
                first = false
                elems.append(const(syntax))
            case .Keyword(let keyword):
                if !first {
                    elems.append(_OptSpace[i])
                }
                first = false
                let k = const(keyword)
                add {
                    prioritise(terminal: k, over: Var)
                }
                elems.append(k)
            case let .Var(v, raised: raised):
                if !first {
                    elems.append(_OptSpace[i])
                }
                first = false
                if abstractSyntax.binders.contains(v) {
                    elems.append(Var[i])
                } else {
                    elems.append(raised ? E_raised[i] : E[i])
                }
            }
            i += 1
        }
        return collectRuleBody(elems)
    }
    
    func syntaxPatternRuleBody(syntaxPattern : SyntaxPattern, concreteSyntax : ConcreteSyntax, E : N, E_raised : N) -> RuleBody
    {
        var elems : [RuleBody] = []
        var i = 0
        var first : Bool = true
        for fragment in concreteSyntax.fragments {
            switch fragment {
            case .Space:
                if !first {
                    elems.append(_OptSpace[i])
                    first = true
                }
            case .Text(let syntax):
                if !first {
                    elems.append(_OptSpace[i])
                }
                first = false
                elems.append(const(syntax))
            case .Keyword(let keyword):
                if !first {
                    elems.append(_OptSpace[i])
                }
                first = false
                let k = const(keyword)
                add {
                    prioritise(terminal: k, over: Var)
                }
                elems.append(k)
            case let .Var(v, raised: raised):
                if !first {
                    elems.append(_OptSpace[i])
                }
                first = false
                if syntaxPattern.containsBinder(v) {
                    elems.append(Var[i])
                } else {
                    elems.append(raised ? E_raised[i] : E[i])
                }
            }
            i += 1
        }
        return collectRuleBody(elems)
    }

    internal static func syntaxPatternNonterminalName(patternIndex : Int, concreteSyntax : Int) -> String {
        return "syntaxpattern-\(patternIndex)-\(concreteSyntax)"
    }
    
    public func addPatternRules(patternIndex : Int, pattern : SyntaxPattern, syntax : [ConcreteSyntax], priorities : Priorities) {
        for i in 0 ..< syntax.count {
            let N = nonterminal(SymbolName(PractalExprGrammar.syntaxPatternNonterminalName(patternIndex: patternIndex, concreteSyntax: i)))
            let concreteSyntax = syntax[i]
            let E = priorities.lookup(concreteSyntax.priority)
            add {
                E.parent.rule {
                    N
                }
                N.rule {
                    syntaxPatternRuleBody(syntaxPattern: pattern, concreteSyntax: concreteSyntax, E: E.child, E_raised: E.raised_child)
                }
            }
        }
    }
    
    public func addConcreteSyntaxRules() {
        var prios : Set<Float> = []
        for (_, css) in syntax {
            for cs in css {
                switch cs.priority {
                case let .Level(p): prios.insert(p)
                default: break
                }
            }
        }
        let priorities = Priorities(prios, grammar: self)
        for (i, (pattern, syntax)) in syntax.enumerated() {
            addPatternRules(patternIndex: i, pattern: pattern, syntax: syntax, priorities: priorities)
        }
    }
    
    public func addConcreteSyntaxSpecRules() {
        add {
            ConcreteSyntaxSpec.rule {
                Repeat1Greedy(_ConcreteSyntaxFragment)
            }
            
            _ConcreteSyntaxFragment.rule {
                OrGreedy(CSF_RaisedVar, CSF_Space, Seq(const("`"), CSF_Var), CSF_Text)
            }
            
            CSF_Space.rule {
                _Space
            }
            
            CSF_Var.rule {
                Id
            }
            
            CSF_RaisedVar.rule {
                Id
            }

            CSF_Text.rule {
                Char
            }
            
        }
    }
    
    public override func build() {
        super.build()
        
        addSpaceRules()
        addIDRules()
        addVariableRules()
        addConstantRules()
        addListRules()
        addConcreteSyntaxRules()
        
        addConcreteSyntaxSpecRules()
        
        add {
            PractalExpr.rule {
                _Expr
            }
            
            _AtomicExpr.rule {
                Variable
            }
            
            _AtomicExpr.rule {
                Constant
            }
            
            _AtomicExpr.rule {
                const("(")
                _OptSpace[0]
                _Expr[1]
                _OptSpace[1]
                const(")")
            }
        }
    }

}


