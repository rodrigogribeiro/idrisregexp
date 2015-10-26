module RegExpParser

import public Lightyear
import public Lightyear.Char
import public Lightyear.Strings

import RegExp

pChar : Parser RegExp
pChar = Chr <$> noneOf "()*+"

pAtom : Parser RegExp
pAtom = foldr Cat Eps <$> many pChar
