//
//  Const.swift
//  
//
//  Created by Steven Obua on 05/08/2021.
//

import Foundation

public struct Const : Hashable, CustomStringConvertible {
    
    public let namespace : Namespace
    public let name : Id
    
    public init(namespace : Namespace = Namespace(), name : Id) {
        self.namespace = namespace
        self.name = name
    }
    
    public init?(qualified : String) {
        let splits = qualified.split(separator: Namespace.SEPARATOR, omittingEmptySubsequences: false)
        if splits.isEmpty { return nil }
        var ids : [Id] = []
        for s in splits {
            guard let id = Id(String(s)) else { return nil }
            ids.append(id)
        }
        self.name = ids.removeLast()
        self.namespace = Namespace(ids)
    }
    
    public var description: String {
        var d = name.description
        for n in namespace.components.reversed() {
            d = "\(n)\(Namespace.SEPARATOR)\(d)"
        }
        return d
    }
    
}
