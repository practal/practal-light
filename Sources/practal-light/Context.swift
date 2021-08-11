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
    
    public var kernel : KernelContext {
        return kcc.current
    }
    
    convenience public init() {
        self.init(KernelContext.root())
    }
    
    @discardableResult
    public func addSyntax(_ pattern : SyntaxPattern, _ concreteSyntax : ConcreteSyntax) -> Bool {
        guard pattern.isPattern else {
            print("pattern is not a pattern")
            return false
        }
        let vars = pattern.vars()
        let concreteSyntax = concreteSyntax.selectVars { v in vars.contains(v) }
        guard !concreteSyntax.hasDuplicateVarOccurrences else {
            print("concrete syntax has duplicate variable occurrences")
            return false
        }
        guard Set(concreteSyntax.vars).count == vars.count else {
            print("some free variables of the abstract syntax do not occur in the concrete syntax")
            return false
        }
        syntax.append((pattern, [concreteSyntax]))
        dirty_syntax = true
        return true
    }
    
    public var parser : PractalExprParser {
        refresh()
        return _parser
    }
    
    public var printer : PrettyPrinter {
        refresh()
        return _printer
    }
    
    @discardableResult
    public func extend(_ op: (Context) -> KernelContext?) -> Bool {
        guard let kc = op(self) else { return false }
        return kcc.append(kc)
    }
    
}
