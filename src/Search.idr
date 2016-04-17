module Search

import RegExp
import SmartCons

%default total
%access public export

-- emptyness test

hasEmptyDec : (e : RegExp) -> Dec (InRegExp [] e)
hasEmptyDec Zero = No (void . inZeroInv)
hasEmptyDec Eps = Yes InEps
hasEmptyDec (Chr c) = No inChrNil
hasEmptyDec (Cat e e') with (hasEmptyDec e)
  hasEmptyDec (Cat e e') | (Yes prf) with (hasEmptyDec e')
    hasEmptyDec (Cat e e') | (Yes prf) | (Yes prf') = Yes (InCat prf prf' Refl)
    hasEmptyDec (Cat e e') | (Yes prf) | (No contra) = No (contra . snd . inCatNil)
  hasEmptyDec (Cat e e') | (No contra) = No (contra . fst . inCatNil)
hasEmptyDec (Alt e e') with (hasEmptyDec e)
  hasEmptyDec (Alt e e') | (Yes prf) = Yes (InAltL prf)
  hasEmptyDec (Alt e e') | (No contra) with (hasEmptyDec e')
    hasEmptyDec (Alt e e') | (No contra) | (Yes prf) = Yes (InAltR prf)
    hasEmptyDec (Alt e e') | (No contra) | (No f) = No (void . either contra f . inAltNil)
hasEmptyDec (Star e) = Yes (InStar (InAltL InEps))


-- derivative definition

deriv : (e : RegExp) -> Char -> RegExp
deriv Zero c = Zero
deriv Eps c = Zero
deriv (Chr c') c with (decEq c' c)
  deriv (Chr c) c  | Yes Refl = Eps
  deriv (Chr c') c | No nprf = Zero
deriv (Alt l r) c = (deriv l c) .|. (deriv r c)
deriv (Star e) c = (deriv e c) .@. (Star e)
deriv (Cat l r) c with (hasEmptyDec l)
  deriv (Cat l r) c | Yes prf = ((deriv l c) .@. r) .|. (deriv r c)
  deriv (Cat l r) c | No nprf = (deriv l c) .@. r

derivSound : InRegExp xs (deriv e x) -> InRegExp (x :: xs) e
derivSound {e = (Chr c)} {x = x} pr with (decEq c x)
  derivSound {e = (Chr c)} {x = x} pr | k = ?rhs
derivSound {e = Zero} pr = void (inZeroInv pr)
derivSound {e = Eps} pr = void (inZeroInv pr)
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
