module RegExp

%default total
%access public export

data RegExp : Type where
  Zero : RegExp
  Eps  : RegExp
  Chr  : Nat -> RegExp
  Cat  : RegExp -> RegExp -> RegExp 
  Alt  : RegExp -> RegExp -> RegExp 
  Star : RegExp -> RegExp 

data InRegExp : List Nat -> RegExp -> Type where
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

inEpsCons : InRegExp (x :: xs) Eps -> Void
inEpsCons InEps impossible

inChrNil : InRegExp [] (Chr c) -> Void
inChrNil InEps impossible

concatNil : Prelude.List.Nil = (xs ++ ys) -> (xs = Prelude.List.Nil , ys = Prelude.List.Nil)
concatNil {xs = []}{ys = []} p = (Refl, Refl)
concatNil {xs = []}{ys = (x :: xs)} p = void (lemma_val_not_nil (sym p))
concatNil {xs = (x :: xs)}{ys = ys} p = void (lemma_val_not_nil (sym p))

inCatNil : InRegExp [] (Cat e e') -> (InRegExp [] e , InRegExp [] e')
inCatNil (InCat x y prf) with (concatNil prf)
  inCatNil (InCat x y prf) | (Refl , Refl) = (x, y)

inAltNil : InRegExp [] (Alt e e') -> Either (InRegExp [] e) (InRegExp [] e')
inAltNil (InAltL x) = Left x
inAltNil (InAltR x) = Right x
