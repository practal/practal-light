//
//  TmWithHolesExt.swift
//
//  Created by Steven Obua on 25/08/2021.
//

import Foundation

extension TmWithHoles {
    
    public static func projection(holes : Int, _ k : Int) -> TmWithHoles {
        return TmWithHoles(holes: holes, .bound(k))
    }
    
    public static func constant(holes : Int, _ bound : Int) -> TmWithHoles {
        return TmWithHoles(holes: holes, .bound(bound + holes))
    }
    
    public static func constant(holes : Int, head : Head, fresh : (Var, Int) -> Var) -> TmWithHoles {
        var params : [Tm] = []
        let binders = head.binders
        let level = binders.count
        let holeArgs = (level ..< level + holes).map { i in Tm.bound(i)}
        for (i, p) in head.params.enumerated() {
            let selected = head.selectBoundVars(param: i, binders: binders)
            let args : [Tm] = selected.map { b in Tm.bound(head.binderIndex(b)!) }
            let ps = args + holeArgs
            let F = Tm.free(fresh(p.var!, ps.count), params: ps)
            params.append(F)
        }
        let tm = Tm.const(head.const, binders: binders, params: params)
        return TmWithHoles(holes: holes, tm)
    }
    
    public static func variable(holes : Int, `var` v: Var, numargs : Int, fresh : (Var, Int) -> Var) -> TmWithHoles {
        var params : [Tm] = []
        let holeArgs = (0 ..< holes).map { i in Tm.bound(i)}
        for k in 0 ..< numargs {
            let name = "\(v.name.id)-arg-\(k)"
            let v = fresh(Var(name)!, holeArgs.count)
            let p = Tm.free(v, params: holeArgs)
            params.append(p)
        }
        let tm = Tm.free(v, params: params)
        return TmWithHoles(holes: holes, tm)
    }
    
    public static func variable(_ v : Var, arity : Int) -> TmWithHoles {
        let bounds = (0 ..< arity).map { i in Tm.bound(i) }
        return TmWithHoles(holes: arity, .free(v, params: bounds))
    }
        
    public static func hoPattern(holes : Int, deps : [Int], fresh : Var) -> TmWithHoles {
        let params = deps.map { d in Tm.bound(d) }
        let tm = Tm.free(fresh, params: params)
        return TmWithHoles(holes: holes, tm)
    }
    
    public static func elimination(holes : Int, _ G : Var, _ deps : [Int]) -> TmWithHoles {
        let params = deps.map { d in Tm.bound(d) }
        let tm = Tm.free(G, params: params)
        return TmWithHoles(holes: holes, tm)
    }
    
    private static func allBounds(holes : Int) -> [Tm] {
        var bounds : [Tm] = []
        for arg in 0 ..< holes {
            bounds.append(.bound(arg))
        }
        return bounds
    }
    
    public static func identify(holes : Int, F : Var, H : Var, arity : Int, fresh : (Var, Int) -> Var) -> TmWithHoles {
        let bounds = allBounds(holes: holes)
        var params : [Tm] = []
        params.append(contentsOf: bounds)
        for i in 0 ..< arity - holes {
            let id = Id("\(F.name.id)-\(i+1)")!
            let F_i = fresh(Var(name: id), bounds.count)
            params.append(.free(F_i, params: bounds))
        }
        return TmWithHoles(holes: holes, .free(H, params: params))
    }
    
    public static func identify(holes : Int, G : Var, H : Var, arity : Int, fresh : (Var, Int) -> Var) -> TmWithHoles {
        let bounds = allBounds(holes: holes)
        var params : [Tm] = []
        for i in 0 ..< arity - holes {
            let id = Id("\(G.name.id)-\(i+1)")!
            let G_i = fresh(Var(name: id), bounds.count)
            params.append(.free(G_i, params: bounds))
        }
        params.append(contentsOf: bounds)
        return TmWithHoles(holes: holes, .free(H, params: params))
    }

}
