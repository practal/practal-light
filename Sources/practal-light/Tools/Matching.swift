//
//  Matching.swift
//  
//
//  Created by Steven Obua on 08/08/2021.
//

import Foundation

/*public struct Matching {
    
    private struct Task {
        
        let boundVarsPattern : [Var : Var]
        
        let boundVarsInstance : [Var : Var]
        
        var pattern : Term
        
        let instance : Term
        
        mutating func substitute(kc : KernelContext, _ v : Var, _ twh : TermWithHoles) {
            
        }
        
    }
        
    public let kc : KernelContext
    
    public func match(pattern : Term, instance : Term) -> Substitution? {
        
        var substitutions : [(Var, TermWithHoles)] = []
        var tasks = [Task(boundVarsPattern: [:], boundVarsInstance: [:], pattern: pattern, instance: instance)]
        
        func addSubstitution(_ v : Var, _ twh : TermWithHoles) {
            substitutions.append((v, twh))
            for i in 0 ..< tasks.count {
                tasks[i].substitute(kc: kc, v, twh)
            }
        }
        
        func solveTask(_ task : Task) -> Bool {
            switch (pattern, instance) {
            case (.constant, .variable): return false
            case let (.constant(const1, binders1, params1), .constant(const2, binders: binders2, params: params2)):
                guard const1 == const2 else { return false }
                let head = kc.constants[const1]!.head
                for (i, param) in params1.enumerated() {
                    let select1 = head.selectBoundVars(param: i, binders: binders1)
                    let select2 = head.selectBoundVars(param: i, binders: binders2)
                    var boundVars1 = task.boundVarsPattern
                    var boundVars2 = task.boundVarsInstance
                    for (j, b1) in select1.enumerated() {
                        let b2 = select2[j]
                        boundVars1[b1] = b2
                        boundVars2[b2] = b1
                    }
                    let task = Task(boundVarsPattern: boundVars1, boundVarsInstance: boundVars2, pattern: param, instance: params2[i])
                    tasks.append(task)
                }
                return true
            case let (.variable(v1, params1), .variable(v2, params2)):
                let w1 = task.boundVarsPattern[v1]
                let w2 = task.boundVarsInstance[v2]
                if w1 != nil && w2 != nil {
                    // both variables are bound
                    return w1 == v2 && w2 == v1
                } else if w1 != nil && w2 == nil {
                    // the pattern is bound and the instance is free
                    return false
                } else if w1 == nil && w2 != nil {
                    // the pattern is free and the instance is bound
                    guard let i = (params1.firstIndex { (term : Term) -> Bool in
                        term == .variable(w2!, params: [])
                    }) else { return false }
                    // we just use the first parameter position found, if there are more we might be missing a possible match
                    
                    return false // we bailout, we cannot deal with this case yet
                } else if w1 == nil && w2 == nil {
                    // both pattern and instance are free variables
                    fatalError()
                }
                fatalError()
            default:
                return false
            }
        }
        
 
        while !tasks.isEmpty {
            let task = tasks.removeLast()
            guard solveTask(task) else { return nil }
        }
        
        var result = Substitution()
        var i = substitutions.count - 1
        while i >= 0 {
            let (v, twh) = substitutions[i]
            let s = kc.substituteSafely(result, in: twh.term, boundVars: Set(twh.holes))!
            result[v] = TermWithHoles(twh.holes, s)
            i -= 1
        }
        
        let freeVars = kc.freeVarsOf(pattern).arity
        
        return result.filter { v, t in
            return freeVars[v] != nil
        }
        
    }
    
}*/

