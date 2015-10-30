module RegExpParser

import public Lightyear
import public Lightyear.Char
import public Lightyear.Strings

import RegExp
import SmartCons

pChar : Parser RegExp
pChar = Chr <$> noneOf "()*+"

pAtom : Parser RegExp
pAtom = foldl1 (.@.) <$> some pChar

pstar : Parser (RegExp -> RegExp)
pstar = const star <$> lexeme (char '*') 

mutual 
  pStar : Parser (RegExp -> RegExp)
  pStar = pstar <|> pure id

  pFactor : Parser RegExp
  pFactor =  pAtom -- <|> (commitTo (parens pExp))
  
  pTerm : Parser RegExp
  pTerm = f <$> pFactor <*!> pStar
          where
            f e g = g e
          
  pExp' : Parser (RegExp -> RegExp)
  pExp' = foldl (.) id <$> many ((flip (.|.)) <$> (lexeme (char '+') *!> pTerm))
  
  pExp : Parser RegExp
  pExp = (\t => \f => f t) <$> pTerm <*!> pExp'
