//
//  Namespace.swift
//  
//
//  Created by Steven Obua on 05/08/2021.
//

import Foundation

public struct Namespace : Hashable {
    
    public static let SEPARATOR : Character = "."
    
    public var components : [Id]
    
    public init(_ components : [Id] = []) {
        self.components = components
    }
    
    public var isEmpty : Bool {
        return components.isEmpty
    }
    
}
