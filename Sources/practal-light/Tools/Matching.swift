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
            //print("substitute \(v) ==> \(tmWithHoles)")
            let newTasks = tasks.compactMap { task in task.apply(subst) }
            guard newTasks.count == tasks.count else { return false }
            guard result.compose(subst) else { return false }
            result[v] = tmWithHoles
            tasks = newTasks
            return true
        }
        
        mutating func addTask(_ task : Task) {
            //print("adding task: \(task)")
            tasks.append(task)
        }
        
        mutating func nextTask() -> Task? {
            if tasks.isEmpty { return nil }
            return tasks.removeLast()
        }
        
    }
        
    public let kc : KernelContext
    
    public func match(patterns : [Tm], instances : [Tm], max_matches : Int, frees : inout FreeVars) -> [TmSubstitution] {
        guard patterns.count == instances.count else { fatalError() }
        
        var _patternFreeVars = FreeVars()
        
        for p in patterns {
            guard frees.add(p) else { return [] }
            _patternFreeVars.add(p)
        }
        
        let patternFreeVars = _patternFreeVars.vars
        
        guard let (instances, renaming) = frees.addFresh(instances) else { return [] }
        
        let constantFreeVars = renaming.codomain
        
        var nextJobs : [Job] = []
        var results : [TmSubstitution] = []

        var job = Job(result: TmSubstitution(), tasks: [])
        for (i, p) in patterns.enumerated() {
            job.addTask(Task(level: 0, pattern: p, instance: instances[i]))
            //print("*** \(p)  ==>  \(instances[i])")
        }
                
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
        
        func couldMatch(pattern  : Tm, constVar : Var) -> Bool {
            switch pattern {
            case let .free(v, params: _):
                if constantFreeVars.contains(v) {
                    return v == constVar
                } else {
                    return true
                }
            case .bound, .const: return false
            }
        }
        
        func couldMatch(pattern : Tm, const : Const) -> Bool {
            switch pattern {
            case let .free(v, params: _): return !constantFreeVars.contains(v)
            case .bound: return false
            case let .const(c, binders: _, params: _): return c == const
            }
        }
        
        func couldMatch(pattern : Tm, constBound index : Int) -> Bool {
            switch pattern {
            case .free: return true
            case let .bound(i): return i == index
            case .const: return false
            }
        }

        func couldMatch(pattern : Tm, bound index : Int) -> Bool {
            return pattern == .bound(index)
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
                job.addTask(task)
                var twhs : [TmWithHoles] = []
                for (i, p) in params1.enumerated() {
                    if couldMatch(pattern: p, bound: index) {
                        twhs.append(TmWithHoles.projection(holes: params1.count, i))
                    }
                }
                return trySubstitutions(v, substs: twhs)
            case let (.free(v, params: params1), .bound(index)): // index >= task.level
                job.addTask(task)
                var twhs : [TmWithHoles] = []
                twhs.append(TmWithHoles.constant(holes: params1.count, index - task.level))
                for (i, p) in params1.enumerated() {
                    if couldMatch(pattern: p, constBound: index) {
                        twhs.append(TmWithHoles.projection(holes: params1.count, i))
                    }
                }
                return trySubstitutions(v, substs: twhs)
            case let (.free(v, params: params1), .const(c, _, params: _)):
                guard let head = kc.constants[c]?.head else { return false }
                job.addTask(task)
                var twhs : [TmWithHoles] = []
                let twh = TmWithHoles.constant(holes: params1.count, head: head) { v, a in frees.addFresh(v, arity: a) }
                twhs.append(twh)
                for (i, p) in params1.enumerated() {
                    if couldMatch(pattern: p, const: c) {
                        twhs.append(TmWithHoles.projection(holes: params1.count, i))
                    }
                }
                return trySubstitutions(v, substs: twhs)
            case let (.free(v1, params: params1), .free(v2, params: params2)):
                job.addTask(task)
                var twhs : [TmWithHoles] = []
                let twh = TmWithHoles.variable(holes: params1.count, var: v2, numargs: params2.count) { v, a in frees.addFresh(v, arity: a) }
                twhs.append(twh)
                for (i, p) in params1.enumerated() {
                    if couldMatch(pattern: p, constVar: v2) {
                        twhs.append(TmWithHoles.projection(holes: params1.count, i))
                    }
                }
                return trySubstitutions(v1, substs: twhs)
            }
        }
                
        let renamingReversed = renaming.reversed()
        
        jobLoop:
        repeat {
            while let task = job.nextTask() {
                guard solveTask(task) else {
                    guard !nextJobs.isEmpty else { return results }
                    job = nextJobs.removeLast()
                    continue jobLoop
                }
            }
            job.result.restrict(patternFreeVars)
            job.result.compose(renamingReversed)
            results.append(job.result)
            guard !nextJobs.isEmpty, results.count < max_matches else {
                return results
            }
            job = nextJobs.removeLast()
        } while true
    }
    
    public func match(patterns : [Tm], instances : [Tm], max_matches : Int = Int.max) -> [TmSubstitution] {
        var frees = FreeVars()
        return match(patterns: patterns, instances: instances, max_matches: max_matches, frees: &frees)
    }

    public func match(pattern : Tm, instance : Tm, max_matches : Int = Int.max) -> [TmSubstitution] {
        return match(patterns: [pattern], instances: [instance], max_matches: max_matches)
    }
        
    public func match1(pattern : Tm, instance : Tm) -> TmSubstitution? {
        return match(pattern: pattern, instance: instance, max_matches: 1).first
    }
}

extension Matching {
    
    public func proveByAxiom(term : Term) -> (axiom : Int, thm : Theorem)? {
        guard let tm = kc.tmOf(term) else { return nil }
        for (i, ax) in kc.axioms.enumerated() {
            let ax = kc.tmOf(ax)!
            guard let subst = match1(pattern: ax, instance: tm) else { continue }
            let th = kc.axiom(i)
            guard let sth = kc.substitute(subst, in: th) else { continue }
            return (axiom: i, thm: sth)
        }
        return nil
    }
    
}

