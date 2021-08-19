//
//  Unification.swift
//
//  Created by Steven Obua on 19/08/2021.
//

import Foundation

public struct Unification {
    
    private struct Task : CustomStringConvertible {
        
        let level : Int
                
        let lhs : Tm
        
        let rhs : Tm
        
        func apply(_ subst : TmSubstitution) -> Task? {
            guard let l = subst.apply(level: level, lhs) else { return nil }
            guard let r = subst.apply(level: level, rhs) else { return nil }
            return Task(level: level, lhs: l, rhs: r)
        }
        
        var description: String {
            return "[\(level)] \(lhs) <=> \(rhs)"
        }
        
        var reversed: Task {
            return Task(level: level, lhs: rhs, rhs: lhs)
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
    
    public func unify(lhs : [Tm], rhs : [Tm], max_unifications : Int, frees : inout FreeVars) -> [TmSubstitution] {
        guard lhs.count == rhs.count else { fatalError() }
        
        var freeVars = FreeVars()
        
        for t in lhs + rhs {
            guard frees.add(t) else { return [] }
            freeVars.add(t)
        }
                
        var nextJobs : [Job] = []
        var results : [TmSubstitution] = []

        var job = Job(result: TmSubstitution(), tasks: [])
        for (i, l) in lhs.enumerated() {
            job.addTask(Task(level: 0, lhs: l, rhs: rhs[i]))
            //print("*** \(p)  <=>  \(instances[i])")
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
                job.addTask(Task(level: level, lhs: param, rhs: params2[i]))
            }
            return true
        }
        
        func couldMatch(pattern : Tm, const : Const) -> Bool {
            switch pattern {
            case .free: return true
            case .bound: return false
            case let .const(c, binders: _, params: _): return c == const
            }
        }

        func couldMatch(pattern : Tm, bound index : Int) -> Bool {
            return pattern == .bound(index)
        }
        func couldMatch(pattern : Tm, constBound index : Int) -> Bool {
            switch pattern {
            case .free: return true
            case let .bound(i): return i == index
            case .const: return false
            }
        }

        func solveTask(_ task : Task) -> Bool {
            switch (task.lhs, task.rhs) {
            case (.const, .free): return solveTask(task.reversed)
            case (.const, .bound): return false
            case (.bound, .const): return false
            case let (.const(const1, binders1, params1), .const(const2, binders: binders2, params: params2)):
                guard const1 == const2, binders1.count == binders2.count else { return false }
                let sublevel = binders1.count + task.level
                return solve(level: sublevel, params1: params1, params2: params2)
            case let (.bound(index1), .bound(index2)): return index1 == index2
            case (.bound, .free): return solveTask(task.reversed)
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
                /*job.addTask(task)
                var twhs : [TmWithHoles] = []
                let twh = TmWithHoles.variable(holes: params1.count, var: v2, numargs: params2.count) { v, a in frees.addFresh(v, arity: a) }
                twhs.append(twh)
                for (i, p) in params1.enumerated() {
                    if couldMatch(pattern: p, constVar: v2) {
                        twhs.append(TmWithHoles.projection(holes: params1.count, i))
                    }
                }
                return trySubstitutions(v1, substs: twhs)*/
                fatalError()
            }
        }
                        
        let fvs = freeVars.vars
        
        jobLoop:
        repeat {
            while let task = job.nextTask() {
                guard solveTask(task) else {
                    guard !nextJobs.isEmpty else { return results }
                    job = nextJobs.removeLast()
                    continue jobLoop
                }
            }
            job.result.restrict(fvs)
            results.append(job.result)
            guard !nextJobs.isEmpty, results.count < max_unifications else {
                return results
            }
            job = nextJobs.removeLast()
        } while true
    }
    
    public func unify(lhs : [Tm], rhs : [Tm], max_unifications : Int = Int.max) -> [TmSubstitution] {
        var frees = FreeVars()
        return unify(lhs: lhs, rhs: rhs, max_unifications: max_unifications, frees: &frees)
    }

    public func unify(lhs : Tm, rhs : Tm, max_unifications : Int = Int.max) -> [TmSubstitution] {
        return unify(lhs: [lhs], rhs: [rhs], max_unifications: max_unifications)
    }
        
    public func unify1(lhs : Tm, rhs : Tm) -> TmSubstitution? {
        return unify(lhs: lhs, rhs: rhs, max_unifications: 1).first
    }
}
