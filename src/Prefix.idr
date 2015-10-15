module Prefix

import RegExp
import Search

%default total


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

noPrefixCons : Not (InRegExp [] e) -> Not (Prefix (deriv e x) xs) -> Not (Prefix e (x :: xs))
noPrefixCons nnil nder pr = ?rhs_1
