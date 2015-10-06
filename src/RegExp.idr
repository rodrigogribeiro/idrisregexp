module RegExp

%default total

data RegExp : Type where
  Zero : RegExp
  Eps  : RegExp  
  Chr  : Char -> RegExp
  Cat  : RegExp -> RegExp -> RegExp
  Alt  : RegExp -> RegExp -> RegExp
  Star : RegExp -> RegExp

data HasEmpty : RegExp -> Type where
  HasEps  : HasEmpty Eps
  HasAltL : (r : RegExp) -> 
            HasEmpty l   -> 
            HasEmpty (Alt l r)
  HasAltR : (l : RegExp) -> 
            HasEmpty r   -> 
            HasEmpty (Alt l r)
  HasCat : HasEmpty l   ->
           HasEmpty r   ->
           HasEmpty (Cat l r)
  HasStar : (e : RegExp) -> 
            HasEmpty (Star e)                    

hasEmptyZero : HasEmpty Zero -> Void
hasEmptyZero HasEps impossible

hasEmptyChr : {c : Char} -> HasEmpty (Chr c) -> Void
hasEmptyChr HasEps impossible

hasEmptyCatInv : HasEmpty (Cat l r) -> 
                 (HasEmpty l, HasEmpty r)
hasEmptyCatInv (HasCat l r) = (l , r)                
                                                                                                      
hasEmptyAltInv : HasEmpty (Alt l r) -> 
                 Either (HasEmpty l) (HasEmpty r)
hasEmptyAltInv (HasAltL r pl) = Left pl
hasEmptyAltInv (HasAltR l pr) = Right pr               
                                                                                                            
hasEmptyDec : (e : RegExp) -> Dec (HasEmpty e)
hasEmptyDec Zero = No hasEmptyZero
hasEmptyDec Eps = Yes HasEps
hasEmptyDec (Chr c) = No hasEmptyChr
hasEmptyDec (Alt l r) with (hasEmptyDec l)
 | Yes prf = Yes (HasAltL r prf)
 | No nprf with (hasEmptyDec r)
      | Yes prf' = Yes (HasAltR l prf')
      | No nprf' = No (either nprf nprf' . hasEmptyAltInv)
hasEmptyDec (Cat l r) with (hasEmptyDec l)
                      | Yes prf with (hasEmptyDec r)
                                     | Yes prf' = Yes (HasCat prf prf')
                                     | No nprf' = No (nprf' . snd . hasEmptyCatInv)
                      | No nprf = No (nprf . fst . hasEmptyCatInv)               
hasEmptyDec (Star e) = Yes (HasStar e)


deriv : (e : RegExp) -> Char -> RegExp
deriv Zero c = Zero
deriv Eps c = Zero
deriv (Chr c') c with (decEq c' c)
  deriv (Chr c) c  | Yes Refl = Eps
  deriv (Chr c') c | No nprf = Zero
deriv (Alt l r) c = Alt (deriv l c) (deriv r c)
deriv (Star e) c = Cat (deriv e c) (Star e)
deriv (Cat l r) c with (hasEmptyDec l)
  deriv (Cat l r) c | Yes prf = Alt (Cat (deriv l c) r) (deriv r c)
  deriv (Cat l r) c | No nprf = Cat (deriv l c) r
  
  
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

infixl 4 .|.
  
(.|.) : RegExp -> RegExp -> RegExp
Zero .|. e = e
e .|. Zero = e
e .|. e'   = Alt e e'

infixl 5 .@.

(.@.) : RegExp -> RegExp -> RegExp
Zero .@. e = Zero
Eps .@. e  = e
e .@. Zero = Zero
e .@. Eps  = e
e .@. e'   = Cat e e'

star : RegExp -> RegExp
star Zero = Eps
star Eps = Eps
star e = Star e

altOptSound : (l : RegExp)     ->
              (r : RegExp)     ->
              (xs : List Char) ->
              InRegExp xs (l .|. r) ->
              InRegExp xs (Alt l r)
altOptSound Zero r xs pr = InAltR pr
altOptSound Eps Zero xs pr = InAltL pr
altOptSound Eps Eps xs pr = pr
altOptSound Eps (Chr x) xs pr = pr
altOptSound Eps (Cat x y) xs pr = pr
altOptSound Eps (Alt x y) xs pr = pr
altOptSound Eps (Star x) xs pr = pr
altOptSound (Chr x) Zero xs pr = InAltL pr
altOptSound (Chr x) Eps xs pr = pr
altOptSound (Chr x) (Chr y) xs pr = pr
altOptSound (Chr x) (Cat y z) xs pr = pr
altOptSound (Chr x) (Alt y z) xs pr = pr
altOptSound (Chr x) (Star y) xs pr = pr
altOptSound (Cat x y) Zero xs pr = InAltL pr
altOptSound (Cat x y) Eps xs pr = pr
altOptSound (Cat x y) (Chr z) xs pr = pr
altOptSound (Cat x y) (Cat z w) xs pr = pr
altOptSound (Cat x y) (Alt z w) xs pr = pr
altOptSound (Cat x y) (Star z) xs pr = pr
altOptSound (Alt x y) Zero xs pr = InAltL pr
altOptSound (Alt x y) Eps xs pr = pr
altOptSound (Alt x y) (Chr z) xs pr = pr
altOptSound (Alt x y) (Cat z w) xs pr = pr
altOptSound (Alt x y) (Alt z w) xs pr = pr
altOptSound (Alt x y) (Star z) xs pr = pr
altOptSound (Star x) Zero xs pr = InAltL pr
altOptSound (Star x) Eps xs pr = pr
altOptSound (Star x) (Chr y) xs pr = pr
altOptSound (Star x) (Cat y z) xs pr = pr
altOptSound (Star x) (Alt y z) xs pr = pr
altOptSound (Star x) (Star y) xs pr = pr              
 
altOptComplete : (l : RegExp)  -> 
                 (r : RegExp)  -> 
                 (xs : List Char) -> 
                 InRegExp xs (Alt l r) -> 
                 InRegExp xs (l .|. r)
altOptComplete Zero r xs (InAltL x) = void (inZeroInv x)
altOptComplete Zero r xs (InAltR x) = x
altOptComplete Eps Zero xs (InAltL x) = x
altOptComplete Eps Zero xs (InAltR x) = void (inZeroInv x)
altOptComplete Eps Eps xs pr = pr
altOptComplete Eps (Chr x) xs pr = pr
altOptComplete Eps (Cat x y) xs pr = pr
altOptComplete Eps (Alt x y) xs pr = pr
altOptComplete Eps (Star x) xs pr = pr
altOptComplete (Chr x) Zero xs (InAltL y) = y
altOptComplete (Chr x) Zero xs (InAltR y) = void (inZeroInv y)
altOptComplete (Chr x) Eps xs pr = pr
altOptComplete (Chr x) (Chr y) xs pr = pr
altOptComplete (Chr x) (Cat y z) xs pr = pr
altOptComplete (Chr x) (Alt y z) xs pr = pr
altOptComplete (Chr x) (Star y) xs pr = pr
altOptComplete (Cat x y) Zero xs (InAltL z) = z
altOptComplete (Cat x y) Zero xs (InAltR z) = void (inZeroInv z)
altOptComplete (Cat x y) Eps xs pr = pr
altOptComplete (Cat x y) (Chr z) xs pr = pr
altOptComplete (Cat x y) (Cat z w) xs pr = pr
altOptComplete (Cat x y) (Alt z w) xs pr = pr
altOptComplete (Cat x y) (Star z) xs pr = pr
altOptComplete (Alt x y) Zero xs (InAltL z) = z
altOptComplete (Alt x y) Zero xs (InAltR z) = void (inZeroInv z)
altOptComplete (Alt x y) Eps xs pr = pr
altOptComplete (Alt x y) (Chr z) xs pr = pr
altOptComplete (Alt x y) (Cat z w) xs pr = pr
altOptComplete (Alt x y) (Alt z w) xs pr = pr
altOptComplete (Alt x y) (Star z) xs pr = pr
altOptComplete (Star x) Zero xs (InAltL y) = y
altOptComplete (Star x) Zero xs (InAltR y) = void (inZeroInv y)
altOptComplete (Star x) Eps xs pr = pr
altOptComplete (Star x) (Chr y) xs pr = pr
altOptComplete (Star x) (Cat y z) xs pr = pr
altOptComplete (Star x) (Alt y z) xs pr = pr
altOptComplete (Star x) (Star y) xs pr = pr

catOptSound : (l : RegExp) ->
              (r : RegExp) ->
              (xs : List Char) ->
              InRegExp xs (l .@. r) ->
              InRegExp xs (Cat l r)
catOptSound Zero r xs pr = void (inZeroInv pr)
catOptSound Eps r xs pr = InCat InEps pr Refl
catOptSound (Chr x) Zero xs pr = ?rhs_1
catOptSound (Chr x) Eps xs pr = InCat pr InEps ?rhs_3
catOptSound (Chr x) (Chr y) xs pr = pr
catOptSound (Chr x) (Cat y z) xs pr = pr
catOptSound (Chr x) (Alt y z) xs pr = pr
catOptSound (Chr x) (Star y) xs pr = pr
catOptSound (Cat x y) Zero xs pr = void (inZeroInv pr)
catOptSound (Cat x y) Eps xs pr = InCat pr InEps ?rhseq
catOptSound (Cat x y) (Chr z) xs pr = pr
catOptSound (Cat x y) (Cat z w) xs pr = pr
catOptSound (Cat x y) (Alt z w) xs pr = pr
catOptSound (Cat x y) (Star z) xs pr = pr
catOptSound (Alt x y) Zero xs pr = void (inZeroInv pr)
catOptSound (Alt x y) Eps xs pr = InCat pr InEps ?rhseq1
catOptSound (Alt x y) (Chr z) xs pr = pr
catOptSound (Alt x y) (Cat z w) xs pr = pr
catOptSound (Alt x y) (Alt z w) xs pr = pr
catOptSound (Alt x y) (Star z) xs pr = pr
catOptSound (Star x) Zero xs pr = void (inZeroInv pr)
catOptSound (Star x) Eps xs pr = InCat pr InEps ?rhseq2
catOptSound (Star x) (Chr y) xs pr = pr
catOptSound (Star x) (Cat y z) xs pr = pr
catOptSound (Star x) (Alt y z) xs pr = pr
catOptSound (Star x) (Star y) xs pr = pr
