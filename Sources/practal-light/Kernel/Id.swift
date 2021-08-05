//
//  Id.swift
//
//  Created by Steven Obua on 22/07/2021.
//

import Foundation

public struct Id : Hashable, CustomStringConvertible {

    public let id : String
    
    private static func isLetter(_ c : Character) -> Bool {
        return (c >= "a" && c <= "z") || (c >= "A" && c <= "Z")
    }

    private static func isDigit(_ c : Character) -> Bool {
        return (c >= "0" && c <= "9")
    }
    
    private static func isValid(_ id : String) -> Bool {
        guard !id.isEmpty else { return false }
        guard (id.allSatisfy { c in
            isLetter(c) || isDigit(c) || c == "-"
        }) else { return false }
        guard isLetter(id.first!) else { return false }
        guard id.last != "-" else { return false }
        return !id.contains("--")
    }
        
    public init?(_ id : String) {
        guard Id.isValid(id) else { return nil }
        self.id = id
    }
    
    public var description: String {
        return id
    }
    
}
