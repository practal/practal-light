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
    @Sym var CSF_Text : T

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
                Seq(_Expr, RepeatGreedy(Seq(_OptSpace, _Expr)))
            }
            
            ExprList.rule { }
                        
            Const.rule {
                Id
            }
                        
            Constant.rule {
                Const
                VarList
                const(".")
                _OptSpace[0]
                ExprList
                _OptSpace[1]
            }
        }
    }
    
    public func addConcreteSyntaxSpecRules() {
        add {
            ConcreteSyntaxSpec.rule {
                Repeat1Greedy(_ConcreteSyntaxFragment)
            }
            
            _ConcreteSyntaxFragment.rule {
                OrGreedy(CSF_Var, CSF_Space, CSF_Text)
            }
            
            CSF_Space.rule {
                _Space
            }
            
            CSF_Var.rule {
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
        
        addConcreteSyntaxSpecRules()
        
        add {
            PractalExpr.rule {
                _Expr
            }
            
            _Expr.rule {
                Variable
            }
            
            _Expr.rule {
                Constant
            }
            
            _Expr.rule {
                const("(")
                _OptSpace[0]
                _Expr[1]
                _OptSpace[1]
                const(")")
            }
        }
    }

}
