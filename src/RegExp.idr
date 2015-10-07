module RegExp

%default total

data RegExp : Type where
  Zero : RegExp
  Eps  : RegExp  
  Chr  : Char -> RegExp
  Cat  : RegExp -> RegExp -> RegExp
  Alt  : RegExp -> RegExp -> RegExp
  Star : RegExp -> RegExp  
  
data InRegExp : List Char -> RegExp -> Type where
  InEps : InRegExp [] Eps
  InChr : InRegExp [ a ] (Chr a)
  InCat : InRegExp xs l ->
          InRegExp ys r ->
          zs = xs ++ ys ->
          InRegExp zs (Cat l r)
  InAltL : InRegExp xs l ->
           InRegExp xs (Alt l r)           
  InAltR : InRegExp xs r ->
           InRegExp xs (Alt l r)
  InStar : InRegExp xs (Alt Eps (Cat e (Star e))) ->
           InRegExp xs (Star e)
           
inZeroInv : InRegExp xs Zero -> Void
inZeroInv InEps impossible

inEpsInv : InRegExp xs Eps -> xs = []
inEpsInv InEps = Refl
