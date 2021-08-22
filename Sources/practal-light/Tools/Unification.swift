//
//  Unification.swift
//
//  Created by Steven Obua on 19/08/2021.
//

import Foundation

public struct Unification {
    
    private enum HeadType {
        case bound
        case const
        case free
        
        static func of(_ tm : Tm, level : Int) -> HeadType {
            switch tm {
            case let .bound(index): return index < level ? .bound : .const
            case .free: return .free
            case .const: return .const
            }
        }
    }
    
    private enum Case {
        case bb
        case bc
        case cb
        case bf
        case fb
        case cc
        case cf
        case fc
        case ff
        
        static func of(_ h1 : HeadType, _ h2 : HeadType) -> Case {
            switch (h1, h2) {
            case (.bound, .bound): return .bb
            case (.bound, .const): return .bc
            case (.const, .bound): return .cb
            case (.bound, .free): return .bf
            case (.free, .bound): return .fb
            case (.const, .const): return .cc
            case (.const, .free): return .cf
            case (.free, .const): return .fc
            case (.free, .free): return .ff
            }
        }
    }
    
    public struct Task : CustomStringConvertible, Hashable {
        
        let level : Int
                
        let lhs : Tm
        
        let rhs : Tm
        
        init(level : Int, lhs : Tm, rhs : Tm) {
            self.level = level
            if Tm.compare(lhs, rhs) <= 0 {
                self.lhs = lhs
                self.rhs = rhs
            } else {
                self.lhs = rhs
                self.rhs = lhs
            }
        }
        
        func apply(_ subst : TmSubstitution) -> Task? {
            guard let l = subst.apply(level: level, lhs) else { return nil }
            guard let r = subst.apply(level: level, rhs) else { return nil }
            return Task(level: level, lhs: l, rhs: r)
        }
        
        public var description: String {
            return "[\(level)] \(lhs) ≟ \(rhs)"
        }
        
        var reversed: Task {
            return Task(level: level, lhs: rhs, rhs: lhs)
        }
        
        private var headTypes: (lhs: HeadType, rhs: HeadType) {
            return (lhs: HeadType.of(lhs, level: level), rhs: HeadType.of(rhs, level: level))
        }
        
        private var `case`: Case {
            let h = headTypes
            return Case.of(h.lhs, h.rhs)
        }
        
        fileprivate var isTrivial : Bool {
            return lhs == rhs
        }
        
    }
    
    fileprivate enum Oracle {
        case fails
        case trivial
        case tasks([Task])
        case branch([Task], Var, [TmWithHoles])
    }

    
    public struct Job : CustomStringConvertible {
        
        private var result : TmSubstitution
        
        private var tasks : Set<Task>
        
        init() {
            result = TmSubstitution()
            tasks = []
        }
        
        var getResult : TmSubstitution {
            return result
        }
        
        var leftTasks : Set<Task> {
            return tasks
        }
        
        mutating func restrict(_ vs : Set<Var>) {
            result.restrict(vs)
        }
        
        mutating func substitute(_ v : Var, _ tmWithHoles : TmWithHoles) -> Bool {
            let subst = TmSubstitution(free: [v : tmWithHoles])
            //print("substitute \(v) ==> \(tmWithHoles)")
            let newTasks = tasks.compactMap { task in task.apply(subst) }
            guard newTasks.count == tasks.count else { return false }
            guard result.compose(subst) else { return false }
            result[v] = tmWithHoles
            tasks = Set(newTasks)
            return true
        }
                
        mutating func addTask(_ task : Task) {
            tasks.insert(task)
        }
        
        fileprivate mutating func nextTask(criterium : (Task) -> Oracle?) -> Oracle? {
            for task in tasks {
                guard let oracle = criterium(task) else {
                    continue
                }
                tasks.remove(task)
                return oracle
            }
            return nil
        }
        
        mutating func nextTask() -> Task? {
            guard !tasks.isEmpty else { return nil }
            return tasks.removeFirst()
        }
        
        public var description: String {
            var d = "Job (\(tasks.count) tasks left): \(result)\n"
            for task in tasks {
                d.append("--- \(task)\n")
            }
            return d
        }
        
        
        
    }
    
        
    public let kc : KernelContext
    
    public func unify(lhs : [Tm], rhs : [Tm], frees : inout FreeVars) -> [Job] {
        guard lhs.count == rhs.count else { fatalError() }
        
        var freeVars = FreeVars()
        
        for t in lhs + rhs {
            guard frees.add(t) else { return [] }
            freeVars.add(t)
        }
                
        var nextJobs : [Job] = []
        var results : [Job] = []

        var job = Job()
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
        
        func makeTasks(level : Int, params1 : [Tm], params2 : [Tm]) -> [Task] {
            var tasks : [Task] = []
            for (i, p1) in params1.enumerated() {
                let p2 = params2[i]
                tasks.append(Task(level: level, lhs: p1, rhs: p2))
            }
            return tasks
        }
        
        func findOracleTopPrio(for task : Task) -> Oracle? {
            guard !task.isTrivial else { return .trivial }
            switch (task.lhs, task.rhs) {
            case let (.bound(index1), .bound(index2)):
                return index1 == index2 ? .trivial : .fails
            case (.bound, .const): return .fails
            case (.const, .bound): fatalError()
            case (.free, .bound): fatalError()
            case let (.bound(index), .free(v, params: params)) where index < task.level:
                var twhs : [TmWithHoles] = []
                for (i, p) in params.enumerated() {
                    if couldMatch(pattern: p, bound: index) {
                        twhs.append(TmWithHoles.projection(holes: params.count, i))
                    }
                }
                return .branch([task], v, twhs)
            case let (.bound(index), .free(v, params: params)) where index >= task.level:
                var twhs : [TmWithHoles] = []
                twhs.append(TmWithHoles.constant(holes: params.count, index - task.level))
                for (i, p) in params.enumerated() {
                    if couldMatch(pattern: p, constBound: index) {
                        twhs.append(TmWithHoles.projection(holes: params.count, i))
                    }
                }
                return .branch([task], v, twhs)
            case let (.const(const1, binders1, params1), .const(const2, binders2, params2)):
                if const1 != const2 || binders1.count != binders2.count || params1.count != params2.count {
                    return .fails
                } else {
                    let sublevel = binders1.count + task.level
                    return .tasks(makeTasks(level: sublevel, params1: params1, params2: params2))
                }
            case let (tm, .free(v, params: [])) where !tm.freeVars().contains(v):
                guard let tm = tm.toZeroLevel(level: task.level) else { return .fails }
                let twh = TmWithHoles(holes: 0, tm)
                return .branch([], v, [twh])
            case let (.free(v, params: []), tm) where !tm.freeVars().contains(v):
                guard let tm = tm.toZeroLevel(level: task.level) else { return .fails }
                let twh = TmWithHoles(holes: 0, tm)
                return .branch([], v, [twh])
            case let (.const, .free(v, params: [])) where task.lhs.occursForSure(v):
                return .fails
            case let (.free(v, params: []), .const) where task.rhs.occursForSure(v):
                return .fails
            default: return nil
            }
        }
        
        func findOracleBottomPrio(for task : Task) -> Oracle? {
            switch (task.lhs, task.rhs) {
            case let (.const(c, _, params: _), .free(v, params: params)):
                guard let head = kc.constants[c]?.head else { return .fails }
                var twhs : [TmWithHoles] = []
                let twh = TmWithHoles.constant(holes: params.count, head: head) { v, a in frees.addFresh(v, arity: a) }
                twhs.append(twh)
                for (i, p) in params.enumerated() {
                    if couldMatch(pattern: p, const: c) {
                        twhs.append(TmWithHoles.projection(holes: params.count, i))
                    }
                }
                return .branch([task], v, twhs)
            default: return nil
            }
        }

        
        func nextOracle() -> Oracle? {
            if let t = (job.nextTask { t in findOracleTopPrio(for: t) }) {
                return t
            } else {
                if let t = (job.nextTask { t in findOracleBottomPrio(for: t) }) {
                    return t
                } else {
                    return nil
                }
            }
        }
        
        func solveOracle(_ oracle : Oracle) -> Bool {
            switch oracle {
            case .trivial: return true
            case .fails: return false
            case let .tasks(tasks):
                for task in tasks { job.addTask(task) }
                return true
            case let .branch(tasks, v, twhs):
                for task in tasks { job.addTask(task) }
                return trySubstitutions(v, substs: twhs)
            }
        }
                        
        let fvs = freeVars.vars
        
        var sizeBound = 1
        for l in lhs {
            sizeBound += l.size
        }
        for r in rhs {
            sizeBound += r.size
        }
        sizeBound *= 10

        
        jobLoop:
        repeat {
            while let oracle = nextOracle() {
                guard job.getResult.size < sizeBound, solveOracle(oracle) else {
                    guard !nextJobs.isEmpty else { return results }
                    job = nextJobs.removeLast()
                    //print("discarded job")
                    continue jobLoop
                }
                //print("job has \(job.leftTasks.count) tasks, size is \(job.getResult.size)")
                //print("\(job)")
            }
            /*var r = job.getResult
            r.restrict(fvs)*/
            job.restrict(fvs)
            results.append(job)
            //print("found result no. \(results.count)")
            guard !nextJobs.isEmpty else {
                return results
            }
            job = nextJobs.removeLast()
        } while true
    }
    
    public func unify(lhs : [Tm], rhs : [Tm]) -> [Job] {
        var frees = FreeVars()
        return unify(lhs: lhs, rhs: rhs, frees: &frees)
    }

    public func unify(lhs : Tm, rhs : Tm) -> [Job] {
        return unify(lhs: [lhs], rhs: [rhs])
    }
        
}
