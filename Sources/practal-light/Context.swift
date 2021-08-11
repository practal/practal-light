//
//  Context.swift
//  
//
//  Created by Steven Obua on 06/08/2021.
//

import Foundation

public final class Context {
        
    private var kcc : KCChain
    private var syntax : Syntax
    private var dirty_syntax : Bool
    private var _parser : PractalExprParser
    private var _printer : PrettyPrinter

    public init(_ kc : KernelContext) {
        kcc = KCChain(kc)
        syntax = []
        dirty_syntax = true
        _parser = PractalExprParser(syntax: syntax)
        _printer = PrettyPrinter(patterns: syntax)
    }
    
    private func refresh() {
        if dirty_syntax {
            _parser = PractalExprParser(syntax: syntax)
            _printer = PrettyPrinter(patterns: syntax)
            dirty_syntax = false
        }
    }
    
    public var kernelContext : KernelContext {
        return kcc.current
    }
    
    convenience public init() {
        self.init(KernelContext.root())
    }
    
    @discardableResult
    public func addSyntax(_ pattern : SyntaxPattern, _ concreteSyntax : ConcreteSyntax) -> Bool {
        guard pattern.isPattern else { return false }
        
        fatalError()
    }
    
    @discardableResult
    public func extend(_ extension: (Context) -> KernelContext?) -> Bool {
        fatalError()
    }
    
}
