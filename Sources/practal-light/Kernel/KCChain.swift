//
//  KCChain.swift
//  
//
//  Created by Steven Obua on 05/08/2021.
//

import Foundation

public struct KCChain {
    
    private var _contexts : [KernelContext]
        
    public init(_ contexts : KernelContext...) {
        self._contexts = contexts
    }
    
    public var contexts : [KernelContext] {
        return _contexts
    }
    
    @discardableResult
    public mutating func append(_ context : KernelContext) -> Bool {
        if let last = _contexts.first {
            guard context.parent == last.uuid else { return false }
            _contexts.append(context)
            return true
        } else {
            _contexts = [context]
            return true
        }
    }
    
    public mutating func squash(from : Int? = nil, to : Int? = nil) -> KernelContext? {
        let from = from ?? 0
        let to = to ?? _contexts.count
        guard from < to && from >= 0 && to <= contexts.count else { return nil }
        guard let squashed = KernelContext(squash: _contexts[from ..< to]) else { return nil }
        _contexts[from ..< to] = [squashed]
        return squashed
    }
    
}
