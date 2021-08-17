//
//  Matching.swift
//  
//
//  Created by Steven Obua on 08/08/2021.
//

import Foundation

public struct Matching {
    
    private struct Task : CustomStringConvertible {
        
        let level : Int
                
        let pattern : Tm
        
        let instance : Tm
        
        func apply(_ subst : TmSubstitution) -> Task? {
            guard let s = subst.apply(level: level, pattern) else { return nil }
            return Task(level: level, pattern: s, instance: instance)
        }
        
        var description: String {
            return "[\(level)] \(pattern) => \(instance)"
        }
                
    }
    
    private struct Job {
        
        var result : TmSubstitution
        
        var tasks : [Task]
        
        mutating func substitute(_ v : Var, _ tmWithHoles : TmWithHoles) -> Bool {
            let subst = TmSubstitution(free: [v : tmWithHoles])
            print("substitute \(v) ==> \(tmWithHoles)")
            let newTasks = tasks.compactMap { task in task.apply(subst) }
            guard newTasks.count == tasks.count else { return false }
            guard result.compose(subst) else { return false }
            result[v] = tmWithHoles
            tasks = newTasks
            return true
        }
        
        mutating func addTask(_ task : Task) {
            print("adding task: \(task)")
            tasks.append(task)
        }
        
        mutating func nextTask() -> Task? {
            if tasks.isEmpty { return nil }
            return tasks.removeLast()
        }
        
    }
        
    public let kc : KernelContext
    
    public func match(pattern : Tm, instance : Tm, frees : inout FreeVars) -> [TmSubstitution] {
        
        guard frees.add(pattern) else { return [] }
        
        guard let (instance, instanceRenaming) = frees.addFresh(instance) else { return [] }
        
        let constantFreeVars = instance.freeVars()
        
        var nextJobs : [Job] = []
        var results : [TmSubstitution] = []

        var job = Job(result: TmSubstitution(), tasks: [Task(level: 0, pattern: pattern, instance: instance)])
                
        func trySubstitutions( _ v : Var, substs : [TmWithHoles]) -> Bool {
            var newJobs : [Job] = []
            for s in substs {
                var newJob = job
                guard newJob.substitute(v, s) else { continue }
                newJobs.append(newJob)
            }
            if newJobs.isEmpty { return false }
            job = newJobs.first!
            nextJobs.append(contentsOf: newJobs.dropFirst())
            return true
        }
        
        func solve(level : Int, params1 : [Tm], params2 : [Tm]) -> Bool {
            guard params1.count == params2.count else { return false }
            for (i, param) in params1.enumerated() {
                job.addTask(Task(level: level, pattern: param, instance: params2[i]))
            }
            return true
        }
        
        func solveTask(_ task : Task) -> Bool {
            switch (task.pattern, task.instance) {
            case (.const, .free): return false
            case (.const, .bound): return false
            case let (.const(const1, binders1, params1), .const(const2, binders: binders2, params: params2)):
                guard const1 == const2, binders1.count == binders2.count else { return false }
                let sublevel = binders1.count + task.level
                return solve(level: sublevel, params1: params1, params2: params2)
            case (.bound, .const): return false
            case let (.bound(index1), .bound(index2)): return index1 == index2
            case (.bound, .free): return false
            case let (.free(v, params1), _) where constantFreeVars.contains(v):
                switch task.instance {
                case let .free(w, params: params2) where v == w && params2.count == params1.count:
                    return solve(level: task.level, params1: params1, params2: params2)
                default: return false
                }
            case let (.free(v, params: params1), .bound(index)) where index < task.level:
                guard let k = (params1.firstIndex { (tm : Tm) -> Bool in
                    tm == .bound(index)
                }) else { return false }
                // todo: we just use the first parameter position found, if there are more we might be missing a possible match
                let twh = TmWithHoles.projection(holes: params1.count, k)
                return job.substitute(v, twh)
            case let (.free(v, params: params1), .bound(index)): // index >= task.level
                // todo: we are just taking the simplest possibility here, projections might also be candidates, and we would miss them
                let twh = TmWithHoles.constant(holes: params1.count, index - task.level)
                return job.substitute(v, twh)
            case let (.free(v, params: params1), .const(c, _, params: _)):
                guard let head = kc.constants[c]?.head else { return false }
                let twh = TmWithHoles.constant(holes: params1.count, head: head) { v, a in frees.addFresh(v, arity: a) }
                job.addTask(task)
                return trySubstitutions(v, substs: [twh])
            case let (.free(v1, params: params1), .free(v2, params: params2)):
                let twh = TmWithHoles.variable(holes: params1.count, var: v2, numargs: params2.count) { v, a in frees.addFresh(v, arity: a) }
                job.addTask(task)
                return trySubstitutions(v1, substs: [twh])
            }
        }
        
        jobLoop:
        repeat {
            while let task = job.nextTask() {
                guard solveTask(task) else {
                    guard !nextJobs.isEmpty else { return results }
                    job = nextJobs.removeLast()
                    continue jobLoop
                }
            }
            job.result.restrict(pattern.freeVars())
            job.result.compose(instanceRenaming.reversed())
            results.append(job.result)
            guard !nextJobs.isEmpty else {
                return results
            }
            job = nextJobs.removeLast()
        } while true
        fatalError("internal error")
    }
    
    public func match(pattern : Tm, instance : Tm) -> [TmSubstitution] {
        var frees = FreeVars()
        return match(pattern: pattern, instance: instance, frees: &frees)
    }
    
}

extension Matching {
    
    public func proveByAxiom(term : Term) -> (axiom : Int, thm : Theorem)? {
        guard let tm = kc.tmOf(term) else { return nil }
        for (i, ax) in kc.axioms.enumerated() {
            let ax = kc.tmOf(ax)!
            guard let subst = match(pattern: ax, instance: tm).first else { continue }
            let th = kc.axiom(i)
            guard let sth = kc.substitute(subst, in: th) else { continue }
            return (axiom: i, thm: sth)
        }
        return nil
    }
    
}

