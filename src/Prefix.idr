module Prefix

import RegExp
import Search

%default total
%access public export


-- very simple inversion lemma

lemma_cons_inv : {A : Type} -> {x : A} -> {xs : List A} ->
                               {y : A} -> {ys : List A} ->
                               (x :: xs) = (y :: ys) -> (x = y, xs = ys)
lemma_cons_inv Refl = (Refl , Refl)

-- defining prefixes of a string

data Prefix : (e : RegExp) -> (xs : List Char) -> Type where
  MkPrefix : (ys : List Char)     ->
             (zs : List Char)     ->
             (eq : xs = ys ++ zs) ->
             (re : InRegExp ys e) ->
             Prefix e xs

noPrefixNil : Not (InRegExp [] e) -> Not (Prefix e [])
noPrefixNil ne (MkPrefix [] zs eq re) = ne re
noPrefixNil ne (MkPrefix (x :: xs) zs eq re) = lemma_val_not_nil (sym eq)

noPrefixCons : Not (InRegExp [] e) -> Not (Prefix.Prefix (deriv e x) xs) -> Not (Prefix.Prefix e (x :: xs))
noPrefixCons nnil nder (MkPrefix [] zs eq re) = nnil re
noPrefixCons nnil nder (MkPrefix (y :: ys) zs eq re) with (lemma_cons_inv eq)
  noPrefixCons {x = y}{xs = ys ++ zs} nnil nder (MkPrefix (y :: ys) zs eq re)
    | (Refl , Refl) = nder (MkPrefix ys zs Refl (derivComplete re))


-- prefix decidability

prefixDec : (e : RegExp) -> (xs : List Char) -> Dec (Prefix e xs)
prefixDec e [] with (hasEmptyDec e)
  prefixDec e [] | (Yes prf) = Yes (MkPrefix [] [] Refl prf)
  prefixDec e [] | (No contra) = No (noPrefixNil contra)
prefixDec e (x :: xs) with (hasEmptyDec e)
  prefixDec e (x :: xs) | (Yes prf) = Yes (MkPrefix [] (x :: xs) Refl prf)
  prefixDec e (x :: xs) | (No contra) with (prefixDec (deriv e x) xs)
    prefixDec e (x :: xs) | (No contra) | (Yes (MkPrefix ys zs eq re))
      = Yes (MkPrefix (x :: ys) zs (cong {f = (\ ks => x :: ks)} eq) (derivSound re))
    prefixDec e (x :: xs) | (No contra) | (No contra1) = No (noPrefixCons contra contra1)
