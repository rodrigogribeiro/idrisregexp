module RegExpParser

import ParseLib
import RegExp

pChar : Parser Char RegExp
pChar = Chr <$> pSatisfy p
          where
            p c =  not ((elem c (unpack "()+*")) || (isSpace c))

pWord : Parser Char RegExp
pWord = f <$> pMany pChar
        where
          f [] = Eps
          f xs = foldl1 Cat xs


mutual
  pAtom : Parser Char RegExp
  pAtom = pWord <??> (const Star <$> pSym '*') <|>
          pPack l pExp r
          where
            l = unpack "("
            r = unpack ")"

  pExp : Parser Char RegExp
  pExp = pChainL pPlus pAtom
         where
           pPlus = const Alt <$> pSym '+'

