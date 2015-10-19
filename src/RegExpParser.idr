module RegExpParser

import ParseLib
import RegExp

pChar : Parser Char RegExp
pChar = Chr <$> pSatisfy p
          where
            p c = not (elem c (unpack "()+*"))

pWord : Parser Char RegExp
pWord = (foldl1 Cat) <$> pMany1 pChar
