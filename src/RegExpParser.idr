module RegExpParser

import ParseLib
import RegExp

pChar : Parser Char RegExp
pChar = Chr <$> pSatisfy p
          where
            p c = not (elem c (unpack "()+*"))

pWord : Parser Char RegExp
pWord = (foldl1 Cat) <$> pMany1 pChar


pAtom : Parser Char RegExp
pAtom = pWord <??> (const Star <$> pSym '*') <|>
        pPack l pAtom r
        where
          l = unpack "("
          r = unpack ")"

pExp : Parser Char RegExp
pExp = pChainl pPlus pAtom
       where
         pPlus = const Alt <$> pSym '+'
