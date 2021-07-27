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
    
    private let constants : [Const : ConstSyntax]
    
    public init(constants : [Const : ConstSyntax]) {
        self.constants = constants
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
            }
                        
            Variable.rule {
                Var
                const("[")
                VarList
                const("]")
            }

            Variable.rule {
                Var
            }
                        
            _VarList1.rule {
                Var
            }
            
            _VarList1.rule {
                _VarList1[1]
                _OptSpace[0]
                const(",")
                _OptSpace[1]
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
        }
    }
    
    public func addConstantRules() {
        add {
            ExprList.rule {
                Seq(_AtomicExpr, RepeatGreedy(Seq(_OptSpace, _AtomicExpr)))
            }
            
            ExprList.rule { }
                        
            Const.rule {
                Id
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
        
        init(constants : [Const : ConstSyntax], grammar : PractalExprGrammar) {
            var prios : Set<Float> = []
            for (_, syntax) in constants {
                for cs in syntax.concreteSyntaxes {
                    if let p = cs.priority {
                        prios.insert(p)
                    }
                }
            }
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
    
    public let CONST_CONCRETE_PREFIX = "const-concrete-"

    public func addConstSyntaxRules(const : Const, syntax : ConstSyntax, priorities : Priorities) {
        guard let syntax = constants[const] else { return }
        for i in 0 ..< syntax.concreteSyntaxes.count {
            let concrete_const = nonterminal(SymbolName("\(CONST_CONCRETE_PREFIX)\(i)-\(const.id)"))
            let concreteSyntax = syntax.concreteSyntaxes[i]
            let E = priorities.lookup(concreteSyntax.priority)
            add {
                E.parent.rule {
                    concrete_const
                }
                concrete_const.rule {
                    constConcreteRuleBody(abstractSyntax: syntax.abstractSyntax, concreteSyntax: concreteSyntax, E: E.child, E_raised: E.raised_child)
                }
            }
        }
    }
    
    public func addConcreteSyntaxRules() {
        let priorities = Priorities(constants: constants, grammar: self)
        for (const, syntax) in constants {
            addConstSyntaxRules(const: const, syntax: syntax, priorities: priorities)
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


