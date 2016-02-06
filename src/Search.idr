module Search

import RegExp
import SmartCons

%default total

-- emptyness test

hasEmpty : (e : RegExp) -> Either (InRegExp [] e) (NotInRegExp [] e)
hasEmpty Zero = Right NotInZero
hasEmpty Eps = Left InEps
hasEmpty (Chr c) = Right (NotInChr (lemma_val_not_nil . sym))
hasEmpty (Cat l r) with (hasEmpty l)
  hasEmpty (Cat l r) | Left pr with (hasEmpty r)
    hasEmpty (Cat l r) | Left pr | (Left pr') = Left (InCat pr pr' Refl)
    hasEmpty (Cat l r) | Left pr | (Right pr') = Right (NotInCat Refl (Right (pr, pr')))
  hasEmpty (Cat l r) | Right pr = Right (NotInCat Refl (Left pr))
hasEmpty (Alt l r) with (hasEmpty l)
  hasEmpty (Alt l r) | (Left pr) = Left (InAltL pr)
  hasEmpty (Alt l r) | (Right pr) with (hasEmpty r)
    hasEmpty (Alt l r) | (Right pr) | (Left pr') = Left (InAltR pr')
    hasEmpty (Alt l r) | (Right pr) | (Right pr') = Right (NotInAlt pr pr')
hasEmpty (Star e) = Left (InStar (InAltL InEps))
hasEmpty (Comp e) with (hasEmpty e)
  hasEmpty (Comp e) | (Left pr) = Right (NotInComp pr)
  hasEmpty (Comp e) | (Right pr) = Left (InComp pr)

-- derivative definition

deriv : (e : RegExp) -> Char -> RegExp
deriv Zero c = Zero
deriv Eps c = Zero
deriv (Chr c') c with (decEq c' c)
  deriv (Chr c) c  | Yes Refl = Eps
  deriv (Chr c') c | No nprf = Zero
deriv (Alt l r) c = (deriv l c) .|. (deriv r c)
deriv (Star e) c = (deriv e c) .@. (Star e)
deriv (Cat l r) c with (hasEmpty l)
  deriv (Cat l r) c | Left prf = ((deriv l c) .@. r) .|. (deriv r c)
  deriv (Cat l r) c | Right nprf = (deriv l c) .@. r
deriv (Comp e) c = Comp (deriv e c)

mutual
  derivInSound : InRegExp xs (deriv e x) -> InRegExp (x :: xs) e
  derivInSound {e = Zero} pr = void (inZeroInv pr) 
  derivInSound {e = Eps} pr = void (inZeroInv pr)
  derivInSound {e = (Chr c)}{xs = xs}{x = x} pr with (decEq c x)
    derivInSound {e = (Chr x)}{xs = xs}{x = x} pr | Yes Refl with (inEpsInv pr)
      derivInSound {e = (Chr x)}{xs = []}{x = x} pr | Yes Refl | Refl = InChr
    derivInSound {e = (Chr c)}{xs = xs}{x = x} pr | No contra = void (inZeroInv pr)
  derivInSound {e = (Cat l r)}{xs = xs}{x = x} pr with (hasEmpty l)
    derivInSound {e = (Cat l r)}{xs = xs}{x = x} pr | (Left pr') 
      with (altOptSound (deriv l x .@. r) (deriv r x) xs pr)
      derivInSound {e = (Cat l r)}{xs = xs}{x = x} pr | (Left pr') | (InAltL pr1) 
        with (catOptSound (deriv l x) r xs pr1)
        derivInSound {e = (Cat l r)}{xs = xs}{x = x} pr | (Left pr') | (InAltL pr1) | 
          (InCat y z prf) = rewrite prf in InCat (derivInSound y) z Refl 
      derivInSound {e = (Cat l r)}{xs = xs}{x = x} pr | (Left pr') | (InAltR pr1) 
           = InCat pr' (derivInSound pr1) Refl
    derivInSound {e = (Cat l r)}{xs = xs}{x = x} pr | (Right pr') 
      with (catOptSound (deriv l x) r xs pr)
      derivInSound {e = (Cat l r)}{xs = xs}{x = x} pr | (Right pr') | (InCat y z prf) 
        = rewrite prf in InCat (derivInSound y) z Refl 
  derivInSound {e = (Alt l r)}{xs = xs}{x = x} pr with (altOptSound (deriv l x) (deriv r x) xs pr)
    derivInSound {e = (Alt x y)} pr | (InAltL pr') = InAltL (derivInSound pr')
    derivInSound {e = (Alt x y)} pr | (InAltR pr') = InAltR (derivInSound pr')
  derivInSound {e = (Star e')}{xs = xs}{x = x} pr with (catOptSound (deriv e' x) (Star e') xs pr)
    derivInSound {e = (Star e')} pr | (InCat z y prf) with (derivInSound z)
      derivInSound {e = (Star e')} pr | (InCat z y prf) | k 
        = rewrite prf in InStar (InAltR (InCat k y Refl))
  derivInSound {e = (Comp x)} (InComp pr) with (derivNotInSound pr)
    derivInSound {e = (Comp x)} (InComp pr) | k = InComp k
  
  derivNotInSound : NotInRegExp xs (deriv e x) -> NotInRegExp (x :: xs) e
  derivNotInSound pr = ?rhs

{-
derivSound : InRegExp xs (deriv e x) -> InRegExp (x :: xs) e
derivSound {e = Zero}{xs = xs}{x = x} pr = void (inZeroInv pr)
derivSound {e = Eps}{xs = xs}{x = x} pr = void (inZeroInv pr)
derivSound {e = (Chr c)}{xs = xs}{x = x} pr with (decEq c x)
  derivSound {e = (Chr c)}{xs = xs}{x = c} pr | (Yes Refl) with (inEpsInv pr)
    derivSound {e = (Chr c)}{xs = []}{x = c} pr | (Yes Refl) | Refl = InChr
  derivSound {e = (Chr c)}{xs = xs}{x = x} pr | (No contra) = void (inZeroInv pr)
derivSound {e = (Cat e e')}{xs = xs}{x = x} pr with (hasEmptyDec e)
  derivSound {e = (Cat e e')}{xs = xs}{x = x} pr | (Yes prf)
    with (altOptSound (deriv e x .@. e') (deriv e' x) xs pr)
      derivSound {e = (Cat e e')}{xs = xs}{x = x} pr | (Yes prf) | (InAltL y)
        with (catOptSound (deriv e x) e' xs y)
        derivSound {e = (Cat e e')}{xs = xs}{x = x} pr | (Yes prf) | (InAltL y) | (InCat z w s)
          = rewrite s in InCat (derivSound z) w Refl
      derivSound {e = (Cat e e')}{xs = xs}{x = x} pr | (Yes prf) | (InAltR y) with (derivSound y)
        derivSound {e = (Cat e e')}{xs = xs}{x = x} pr | (Yes prf) | (InAltR y) | k =
          InCat prf k Refl
  derivSound {e = (Cat e e')}{xs = xs}{x = x} pr | (No contra)
    with (catOptSound (deriv e x) e' xs pr)
      derivSound {e = (Cat e e')}{xs = xs}{x = x} pr | (No contra) | (InCat y z prf)
        with (derivSound y)
          derivSound {e = (Cat e e')}{xs = xs}{x = x} pr | (No contra) | (InCat y z p) | k
            = rewrite p in InCat k z Refl
derivSound {e = (Alt e e')}{xs = xs}{x = x} pr with (altOptSound (deriv e x) (deriv e' x) xs pr)
  derivSound {e = (Alt e e')}{xs = xs}{x = x} pr | (InAltL y) = InAltL (derivSound y)
  derivSound {e = (Alt e e')}{xs = xs}{x = x} pr | (InAltR y) = InAltR (derivSound y)
derivSound {e = (Star e)}{xs = xs}{x = x} pr with (catOptSound (deriv e x) (Star e) xs pr)
  derivSound {e = (Star e)}{xs = xs}{x = x} pr | (InCat y z prf) with (derivSound y)
    derivSound {e = (Star e)}{xs = xs}{x = x} pr | (InCat y z prf) | k
      = rewrite prf in InStar (InAltR (InCat k z Refl))


derivComplete : InRegExp (x :: xs) e -> InRegExp xs (deriv e x)
derivComplete {e = Zero}{xs = xs}{x = x} pr = void (inZeroInv pr)
derivComplete {e = Eps}{xs = xs}{x = x} pr with (inEpsInv pr)
  derivComplete {e = Eps}{xs = xs}{x = x} pr | eq = void (lemma_val_not_nil eq)
derivComplete {e = (Chr y)}{xs = xs}{x = x} pr with (decEq y x)
  derivComplete {e = (Chr x)}{xs = []}{x = x} InChr | (Yes Refl) = InEps
  derivComplete {e = (Chr x)}{xs = []}{x = x} InChr | (No contra) = void (contra Refl)
derivComplete {e = (Cat y z)}{xs = xs}{x = x} pr with (hasEmptyDec y)
  derivComplete {e = (Cat y z)}{xs = xs}{x = x} (InCat {xs = []} w s Refl) | (Yes prf)
    = altOptComplete (deriv y x .@. z) (deriv z x) xs (InAltR (derivComplete s))
  derivComplete {e = (Cat y z)}{xs = ys ++ ys1}{x = x} (InCat {xs = (x :: ys)}{ys = ys1} w s Refl)
    | (Yes prf)
      = altOptComplete (deriv y x .@. z) (deriv z x) _
                       (InAltL (catOptComplete (deriv y x) z (ys ++ ys1)
                                (InCat (derivComplete w) s Refl)))
  derivComplete {e = (Cat y z)}{xs = xs}{x = x} (InCat {xs = []} w s eq) | (No contra)
      = void (contra w)
  derivComplete {e = (Cat y z)}{xs = ys ++ ys1}{x = x} (InCat {xs = (x :: ys)}{ys = ys1} w s Refl)
    | (No contra)
      = catOptComplete (deriv y x) z (ys ++ ys1) (InCat (derivComplete w) s Refl)
derivComplete {e = (Alt e e')}{xs = xs}{x = x} (InAltL y)
  = altOptComplete (deriv e x) (deriv e' x) xs (InAltL (derivComplete y))
derivComplete {e = (Alt e e')}{xs = xs}{x = x} (InAltR y)
  = altOptComplete (deriv e x) (deriv e' x) xs (InAltR (derivComplete y))
derivComplete {e = (Star y)}{xs = xs}{x = x} (InStar (InAltL z))
  = void (lemma_val_not_nil (inEpsInv z))
derivComplete {e = (Star y)}{xs = xs}{x = x} (InStar (InAltR (InCat {xs = []} z w Refl)))
  = derivComplete w
derivComplete {e = (Star y)}{xs = ys ++ ys1}{x = x} (InStar (InAltR (InCat {xs = (x :: ys)}{ys = ys1} z w Refl)))
  = catOptComplete (deriv y x) (Star y) (ys ++ ys1) (InCat (derivComplete z) w Refl)
-}
