module Substring

import Prefix
import RegExp
import Search
import SmartCons

%default total
%access public export


data Substring : (e : RegExp) -> (xs : List Char) -> Type where
  MkSubstring : (ys : List Char)           ->
                (ts : List Char)           ->
                (zs : List Char)           ->
                (eq : xs = ys ++ ts ++ zs) ->
                (re : InRegExp ts e)       ->
                Substring e xs

noSubstringNil : Not (Prefix e []) -> Not (Substring e [])
noSubstringNil npre (MkSubstring [] ts zs eq re) = npre (MkPrefix ts zs eq re)
noSubstringNil npre (MkSubstring (y :: ys) ts zs eq re) = lemma_val_not_nil (sym eq)

noSubstringCons : Not (Prefix e (x :: xs))       ->
                  Not (Substring e xs) ->
                  Not (Substring e (x :: xs))
noSubstringCons  npre nsub (MkSubstring [] ts zs eq re) = npre (MkPrefix ts zs eq re)
noSubstringCons  npre nsub (MkSubstring (y :: ys) ts zs eq re) with (lemma_cons_inv eq)
  noSubstringCons  npre nsub (MkSubstring (y :: ys) ts zs eq re) | (Refl, Refl)
    = nsub (MkSubstring ys ts zs Refl re)

subStringDec : (e : RegExp) -> (xs : List Char) -> Dec (Substring e xs)
subStringDec e [] with (hasEmptyDec e)
  subStringDec e [] | (Yes prf) = Yes (MkSubstring [] [] [] Refl prf)
  subStringDec e [] | (No contra) = No (noSubstringNil (noPrefixNil contra))
subStringDec e (x :: xs) with (prefixDec e (x :: xs))
  subStringDec e (x :: xs) | (Yes (MkPrefix ys zs eq re)) = Yes (MkSubstring [] ys zs eq re)
  subStringDec e (x :: xs) | (No contra) with (subStringDec e xs)
    subStringDec e (x :: xs) | (No contra) | (Yes (MkSubstring ys ts zs eq re))
      = Yes (MkSubstring (x :: ys) ts zs (cong eq) re)
    subStringDec e (x :: xs) | (No contra) | (No contra1) = No (noSubstringCons contra contra1)
