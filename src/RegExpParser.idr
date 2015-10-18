module RegExpParser

import ParseLib
import RegExp


pChar : Char -> Parser Char RegExp
pChar c = Chr <$> pSym c
