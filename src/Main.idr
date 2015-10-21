module Main

import Effects
import Effect.StdIO
import Effect.System

interface : {[STDIO, SYSTEM]} Eff ()
interface = do
            putStrLn "IGrep - grep for Idris"
            args <- getArgs
            putStrLn (concat args)
            
            
main : IO ()
main = run interface            
        
