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
pPlus = const Alt <$> lexeme (char '+')

star : Parser (RegExp -> RegExp)
star = const Star <$> lexeme (char '*') 

mutual
  pExp' : Parser (RegExp -> RegExp)
  pExp' = pPlus <*> pExp
  
  pExp : Parser RegExp
  pExp = (\ a => \ f => f a) <$>
         pAtom <*> pFact
         where
           pFact : Parser (RegExp -> RegExp)
           pFact = pExp' <|> star <|> pure id
