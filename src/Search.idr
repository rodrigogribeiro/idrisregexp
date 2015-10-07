module Search

import RegExp
import SmartCons

%default total

-- emptyness test

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


-- derivative definition


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


derivSound : InRegExp xs (deriv e x) -> InRegExp (x :: xs) e
derivSound {e = Zero} pr = void (inZeroInv pr)
derivSound {e = Eps} pr = void (inZeroInv pr)
derivSound {x = x}{e = (Chr x')} pr with (decEq x' x)
  derivSound {x = x}{e = (Chr x)} pr | (Yes Refl) with (inEpsInv pr)
    derivSound {x = x}{e = (Chr x)} pr | (Yes Refl) | Refl = InChr
  derivSound {x = x}{e = (Chr x')} pr | (No contra) = void (inZeroInv pr)
derivSound {e = (Cat e e')}{x} pr with (hasEmptyDec e)
  derivSound {e = (Cat e e')}{x} pr | (Yes prf) = ?rhs 
  derivSound {e = (Cat e e')}{x} pr | (No contra) = ?rhs_2
derivSound {e = (Alt x y)} (InAltL z)  = InAltL (derivSound z)
derivSound {e = (Alt x y)} (InAltR z)  = InAltR (derivSound z)
derivSound {e = (Star x)} (InCat y z prf) with (derivSound y)
  derivSound {e = (Star x)} (InCat y z prf) | pr = ?rhs
