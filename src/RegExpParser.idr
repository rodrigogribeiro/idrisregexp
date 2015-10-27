module RegExpParser

import public Lightyear
import public Lightyear.Char
import public Lightyear.Strings

import RegExp

pChar : Parser RegExp
pChar = Chr <$> noneOf "()*+"

pAtom : Parser RegExp
pAtom = foldr Cat Eps <$> many pChar

pPlus : Parser (RegExp -> RegExp -> RegExp)
pPlus = Alt <$> lexeme (char '+')

star  

mutual
  pExp' : Parser (RegExp -> RegExp)
  pExp' = pPlus <*> pExp
  
  pExp : Parser RegExp
  pExp = pAtom <*> pExp' <|> pAtom <|> pAtom <*> pStar
