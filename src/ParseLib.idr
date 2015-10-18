module ParseLib

-- simple parsing library

%default total

data Parser : (s : Type) -> (a : Type) -> Type where
  pFail   : Parser s a
  pReturn : (v : a) -> Parser s a
  pSym    : (v : s) -> Parser s s


runParser : DecEq s => Parser s a -> List s -> List (a, List s)
runParser pFail s = []
runParser (pReturn v) s = [ (v , s) ]
runParser (pSym v) [] = []
runParser (pSym v) (x :: xs) with (decEq v x)
  runParser (pSym v) (v :: xs) | (Yes Refl) = [(v , xs)]
  runParser (pSym v) (x :: xs) | (No contra) = []

instance DecEq s => Functor (Parser s) where
  map f p = pReturn f :<*>: p

instance DecEq s => Applicative (Parser s) where
  pure = pReturn
  (<*>) l r s = [(f x , ys) | (f , xs) <- runParser]

option : Parser s a -> a -> Parser s a
option p v = p :<|>: pReturn v 

pMany :: Parser s a -> Parser s [a]
pMany p = (::) <$> p :<*>: pMany p  
