module Main

import Effects
import Effect.File
import Effect.StdIO
import Effect.System

import RegExpParser
import RegExp
import Substring


printUsage : {[STDIO]} Eff ()
printUsage = putStrLn "Usage: igrep [REGEXP] [FILELIST]"


search : RegExp -> String -> String
search e s with (subStringDec e (map toNat (unpack s)))
  search e s | Yes _ = s
  search e s | No _ = ""


readFile : { [FILE_IO (OpenFile Read)] } Eff (List String)
readFile = readFile' []
           where
             readFile' : List String -> { [FILE_IO (OpenFile Read)] } Eff (List String)
             readFile' acc = if (not (! eof)) then
                               readFile' (! readLine :: acc)
                             else pure (reverse acc)

searchLines : RegExp -> { [FILE_IO (OpenFile Read)] } Eff (List String)
searchLines e = do
                 ls <- readFile
                 pure (filter (not . isNil . unpack) (map (search e) ls))

searchFile : RegExp -> String -> {[FILE_IO ()]} Eff (List String)
searchFile e f
     = case !(open f Read) of
         True => do
                    xs <- searchLines e
                    close
                    return xs
         False => pure []

searchFiles : RegExp -> List String -> {[STDIO, FILE_IO ()]} Eff (List String)
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
process (x :: e :: fs) with (parse pExp e)
  process (x :: e :: fs) | Left err = putStrLn ("Parser error on:" ++ err)
  process (x :: e :: fs) | Right r
          = do
             ss <- searchFiles r fs
             putStrLn (concat ss)

interface_ : {[STDIO, SYSTEM, FILE_IO ()]} Eff ()
interface_ = do
              putStrLn "IGrep - grep for Idris"
              args <- getArgs
              process args

main : IO ()
main = run interface_
