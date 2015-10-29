module RegExpParser

import public Lightyear
import public Lightyear.Char
import public Lightyear.Strings

import RegExp

infixl 5 <**>

(<**>) :: Parser b -> Parser (b -> a) -> Parser a
p <**> q = (\a => \f => f a) <$> p <*> q

pChar : Parser RegExp
pChar = Chr <$> noneOf "()*+"

pAtom : Parser RegExp
pAtom = foldr Cat Eps <$> many pChar

pPlus : Parser (RegExp -> RegExp -> RegExp)
pPlus = const Alt <$> lexeme (char '+')

star : Parser (RegExp -> RegExp)
star = const Star <$> lexeme (char '*') 

mutual 
  pFactor : Parser RegExp
  pFactor = pAtom <|> parens pExp
  
  pTerm' : Parser RegExp
  pTerm' = Cat <$> pFactor <*> pTerm' <|>
           star <*> pTerm'            <|>
           pure Eps
           
  pTerm : Parser RegExp
  pTerm = Cat <$> pTerm' <*> pTerm    <|>
          pure Eps
          
  pExp' : Parser RegExp
  pExp' = pPlus <*> pTerm <*> pExp'   <|>
          pure Eps
  
  pExp : Parser RegExp
  pExp = Cat <$> pTerm <*> pExp'
