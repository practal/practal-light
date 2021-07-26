//
//  Syntax.swift
//
//  Created by Steven Obua on 26/07/2021.
//

import Foundation

public struct ConcreteSyntax {
    
    public enum Fragment {
        case Slot(Var)
        case Space
        case Text(String)
    }

    public let fragments : [Fragment]
    
    public init(fragments : [Fragment]) {
        self.fragments = fragments
    }

}

public struct AbstractSyntax {
    
    public let const : Const
    
    public let binders : [Var]
    
    public let params : [Var]

}

public struct Syntax {
    
    public let abstract : AbstractSyntax
    
    public let concrete : [ConcreteSyntax]
    
}
