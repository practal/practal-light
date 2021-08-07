//
//  Context.swift
//  
//
//  Created by Steven Obua on 06/08/2021.
//

import Foundation

public final class Context {
    
    public let kc : KernelContext
    
    private init() {
        self.kc = KernelContext.root()
    }
    
}
