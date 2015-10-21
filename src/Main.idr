module Main

import Effects
import Effect.StdIO
import Effect.System

import ParseLib
import RegExpParser

printUsage : {[STDIO, SYSTEM]} Eff ()
printUsage = 
  putStrLn "Usage: igrep REGEXP FILELIST"

process : List String -> {[STDIO, SYSTEM]} Eff ()
process [] = return ()
process [ _ ] = printUsage
process (_ : e : []) = printUsage
process ( _ : e : fs) 
  = case runParser pExp (unpack e) of 
        [] => putStrLn ("Parser error on:" ++ e)
        ((exp,_) :: _) => 
  

interface : {[STDIO, SYSTEM]} Eff ()
interface = do
            putStrLn "IGrep - grep for Idris"
            args <- getArgs
            process args
            
main : IO ()
main = run interface            
        
