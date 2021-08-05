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
    
    public init?(_ qualified : String) {
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
    
    private static func mkC(_ name : String) -> Const {
        return Const("Practal.\(name)")!
    }
    
    public static let c_eq = mkC("eq")
    public static let c_in = mkC("in")

    public static let c_true = mkC("true")
    public static let c_false = mkC("false")
    public static let c_and = mkC("and")
    public static let c_or = mkC("or")
    public static let c_imp = mkC("imp")
    public static let c_not = mkC("not")

    public static let c_ex = mkC("ex")
    public static let c_all = mkC("all")

    public static let c_Prop = Const("Practal.Prop")!

}
