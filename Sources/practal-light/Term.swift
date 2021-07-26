//
//  Term.swift
//  
//  Created by Steven Obua on 25/07/2021.
//

import Foundation

public typealias VarName = String
public typealias ConstId = String

public enum Term {
    case variable(name: VarName, dependencies: [VarName])
    case application(id: ConstId, binders: [VarName], params: [Term])
}
