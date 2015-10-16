module Substring

import Prefix
import RegExp
import Search
import SmartCons
 
%default total


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
 
