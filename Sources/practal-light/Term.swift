//
//  Term.swift
//  
//  Created by Steven Obua on 25/07/2021.
//

import Foundation

public typealias Var = String
public typealias Const = String

public enum Term {
    case variable(Var, dependencies: [Var])
    case constant(Const, binders: [Var], params: [Term])
}
