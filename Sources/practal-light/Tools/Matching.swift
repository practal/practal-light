//
//  Matching.swift
//  
//
//  Created by Steven Obua on 08/08/2021.
//

import Foundation

public struct Matching {
    
    private struct Task {
        
        let level : Int
                
        var pattern : Tm
        
        let instance : Tm
                
    }
        
    public let kc : KernelContext
    
    public func match(pattern : Tm, instance : Tm) -> TmSubstitution? {
        
        var result = TmSubstitution()
        
        var tasks = [Task(level: 0, pattern: pattern, instance: instance)]
        
        func solveTask(_ task : Task) -> Bool {
            switch (task.pattern, task.instance) {
            case (.const, .free): return false
            case (.const, .bound): return false
            case let (.const(const1, binders1, params1), .const(const2, binders: binders2, params: params2)):
                guard const1 == const2, binders1.count == binders2.count, params1.count == params2.count else { return false }
                let sublevel = binders1.count + task.level
                for (i, param) in params1.enumerated() {
                    let task = Task(level: sublevel, pattern: param, instance: params2[i])
                    tasks.append(task)
                }
                return true
            case (.bound, .const): return false
            case let (.bound(index1), .bound(index2)): return index1 == index2
            case (.bound, .free): return false
            case let (.free(v, params: params1), .bound(index)) where index < task.level:
                guard let p = (params1.firstIndex { (tm : Tm) -> Bool in
                    tm == .bound(index)
                }) else { return false }
                // todo: we just use the first parameter position found, if there are more we might be missing a possible match
                fatalError()
            case let (.free(v, params: params1), .bound(index)): // index >= task.level
                fatalError()
            case let (.free(v, params: params1), .const(c, binders, params: params2)):
                fatalError()
            case let (.free(v1, params: params1), .free(v2, params: params2)) where v1 == v2:
                fatalError()
            case let (.free(v1, params: params1), .free(v2, params: params2)): // v1 != v2
                fatalError()
            }
        }
        
        while !tasks.isEmpty {
            let task = tasks.removeLast()
            guard solveTask(task) else { return nil }
        }
                
        result.restrict(pattern.freeVars())
        
        return result
    
    }
    
}

