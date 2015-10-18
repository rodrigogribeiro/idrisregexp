module ParseLib

-- parser definition

record Parser (s : Type)(a : Type) where
  constructor MkParser
  runParser : List s -> List (a, List s)
  
-- basic parsers  
    
pFail : Parser s a
pFail = MkParser (\ s => [])

pReturn : a -> Parser s a
pReturn v = MkParser (\ s => [(v,s)])

pSym : DecEq s => s -> Parser s s
pSym x = MkParser (\ s => 
                     case s of
                       []        => []
                       (y :: ys) => 
                          case decEq x y of
                            Yes prf   => [(x,ys)] 
                            No contra => [])

pSatisfy : (s -> Bool) -> Parser s s
pSatisfy p = MkParser (\ s => case s of
                                [] => []
                                (x :: xs) => 
                                  if p x then [(x,xs)] 
                                    else [])

-- some instances

instance DecEq s => Functor (Parser s) where
  map f p = MkParser (\ s => map (\ (x , ys) => (f x, ys)) 
                                 (runParser p s))

instance DecEq s => Applicative (Parser s) where
  pure = pReturn
  p <*> p' = MkParser (\ s => [ (f y , ys) | (f , xs) <- runParser p s ,
                                             (y , ys) <- runParser p' xs ]) 

instance DecEq s => Alternative (Parser s) where
  empty = pFail
  p <|> p' = MkParser (\ s => runParser p s ++ runParser p' s)


-- derived combinators

pMany : DecEq s => Parser s a -> Parser s (List a)
pMany p = (::) <$> p <*> pMany p <|> pReturn []

pMany1 : DecEq s => Parser s a -> Parser s (List a)
pMany1 p = (::) <$> p <*> pMany p

infixl 5 <**>
infixl 5 <??>

(<**>) : DecEq s => Parser s b -> Parser s (b -> a) -> Parser s a
p <**> q = (\ a => \ f => f a) <$> p <*> q

(<??>) : DecEq s => Parser s a -> Parser s (a -> a) -> Parser s a
p <??> q = p <**> (q <|> pReturn id)

pChoice : DecEq s => List (Parser s a) -> Parser s a
pChoice = foldr (<|>) pFail

pSyms : DecEq s => List s -> Parser s (List s)
pSyms xs = Prelude.Foldable.foldr step val xs
           where
             val = pReturn []
             step x ac = (::) <$> pSym x <*> ac

pPack : DecEq s => List s -> Parser s a -> List s -> Parser s a
pPack l p r = pSyms l *> p <* pSyms r

-- chainl

applyAll : a -> List (a -> a) -> a
applyAll x fs = foldl (\ ac => \ f => f ac) x fs

pChainl : DecEq s => Parser s (a -> a -> a) -> Parser s a -> Parser s a
pChainl op p = applyAll <$> p <*> pMany (flip <$> op <*> p)

-- chainr

pChainR : DecEq s => Parser s (a -> a -> a) -> Parser s a -> Parser s a
pChainR op p = r where r = p <??> (flip <$> op <*> r)

