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
  base : HasEmpty e -> InRegExp [] e
  
