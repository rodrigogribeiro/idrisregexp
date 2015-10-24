module Main

import Effects
import Effect.File
import Effect.StdIO
import Effect.System

import ParseLib
import RegExpParser
import RegExp
import Substring

printUsage : {[STDIO]} Eff ()
printUsage = putStrLn "Usage: igrep [REGEXP] [FILELIST]"
  
search : RegExp -> String -> String
search e s with (subStringDec e (unpack s)) 
  search e s | Yes _ = pack ('\n' :: (unpack s))
  search e s | No _ = ""
  
searchLines : RegExp -> { [FILE_IO (OpenFile Read)] } Eff (List String) 
searchLines e = searchLine []
                where
                  searchLine : List String -> { [FILE_IO (OpenFile Read)] } Eff (List String)
                  searchLine acc = if (not (! eof)) then
                                      let l = !readLine in
                                        pure ((search e l) :: acc)
                                   else pure acc
  
searchFile : RegExp -> String -> {[FILE_IO ()]} Eff (List String)
searchFile e f 
     = case !(open f Read) of
         True => do 
                    xs <- searchLines e
                    close 
                    return xs
         False => pure [""]
  
searchFiles : RegExp -> List String -> {[FILE_IO ()]} Eff (List String)
searchFiles _ [] = return []
searchFiles e (f::fs) 
     = do
         r <-  searchFile e f
         rs <- searchFiles e fs
         return (r ++ ["\n"] ++ rs)
  

process : List String -> {[STDIO, FILE_IO ()]} Eff ()
process [] = return ()
process [ x ] = printUsage
process (x :: e :: []) = printUsage
process (x :: e :: fs) with (runParser pExp (unpack e)) 
  process (x :: e :: fs) | [] = putStrLn ("Parser error on:" ++ e)
  process (x :: e :: fs) | (r :: rs) 
          = do
             ss <- searchFiles (fst r) fs
             putStrLn (concat ss)
 
interface : {[STDIO, SYSTEM, FILE_IO ()]} Eff ()
interface = do
              putStrLn "IGrep - grep for Idris"
              args <- getArgs
              process args
            
main : IO ()
main = run interface            
        
-- Local Variables:
-- idris-packages: ("effects")
-- End:
