module Main

import Effects
import Effect.File
import Effect.StdIO
import Effect.System

import ParseLib
import RegExpParser
import RegExp
import Substring

printUsage : {[STDIO, SYSTEM]} Eff ()
printUsage = 
  putStrLn "Usage: igrep [REGEXP] [FILELIST]"
  
searchLines : RegExp -> {FILE_IO (OpenFile Read)} Eff (List String) 
searchLines e = searchLine []
                where
                  searchLine : List String -> {FILE_IO (OpenFile Read)} Eff (List String)
                  searchLine acc = if (not (! eof)) then 
                                      (do
                                        l <- readLine
                                        case subStringDec e l of
                                           Yes _ => searchLine (l :: acc)
                                           No _  => searchLine acc)
                                    else return acc       
  
searchFile : RegExp -> String -> {[FILE_IO ()]} Eff (List String)
searchFile e f 
     = do
         open f Read
         xs <- searchLines e
         close 
         return xs
  
searchFiles : RegExp -> List String -> {[FILE_IO ()]} Eff (List String)
searchFiles _ [] = return []
searchFiles e (f::fs) 
     = do
         r <-  searchFile e f
         rs <- searchFiles e fs
         return (r ++ rs)
  

process : List String -> {[STDIO, FILE_IO]} Eff ()
process [] = return ()
process [ _ ] = printUsage
process (_ :: e :: []) = printUsage
process ( _ :: e :: fs) 
  = case runParser pExp (unpack e) of 
        [] => putStrLn ("Parser error on:" ++ e)
        ((exp,_) :: _) 
          => do
              rs <- searchFiles e fs
              map putStrLn rs

interface : {[STDIO, SYSTEM, FILE_IO]} Eff ()
interface = do
            putStrLn "IGrep - grep for Idris"
            args <- getArgs
            process args
            
main : IO ()
main = run interface            
        
