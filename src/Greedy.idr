module Greedy

import RegExp
import Search

%default total

-- parse tree definition

data ParseTree : RegExp -> Type where
  PEps : ParseTree Eps
  PChr : (c : Nat) -> ParseTree (Chr c)
  PLeft : ParseTree l -> ParseTree (Alt l r)
  PRight : ParseTree r -> ParseTree (Alt l r)
  PCat : ParseTree l -> ParseTree r -> ParseTree (Cat l r)
  PStar : (ls : List (ParseTree l)) -> ParseTree (Star l)  
  
flatten : ParseTree e -> List Nat
flatten PEps = []
flatten (PChr c) = [ c ]
flatten (PLeft pr) = flatten pr
flatten (PRight pr) = flatten pr
flatten (PCat pr pr') = flatten pr ++ flatten pr'
flatten (PStar prs) = concatMap flatten prs  

-- decidable equality of parse trees

pLeftInv : (PLeft l) = (PLeft l') -> l = l'
pLeftInv Refl = Refl

pRightInv : (PRight r) = (PRight r') -> r = r'
pRightInv Refl = Refl

pLeftRightInv : (PLeft l) = (PRight r) -> Void
pLeftRightInv Refl impossible

pCatInv : (PCat x y) = (PCat x' y') -> (x = x' , y = y')
pCatInv Refl = (Refl , Refl)

pStarInv1 : (PStar []) = (PStar (y :: ys)) -> Void
pStarInv1 Refl impossible

pStarInv2 : (PStar (x :: xs)) = (PStar (y :: ys)) -> (x = y , xs = ys)
pStarInv2 Refl = (Refl , Refl)

implementation DecEq (ParseTree e) where
  decEq PEps PEps = Yes Refl
  decEq (PChr c) (PChr c) = Yes Refl
  decEq (PLeft x) (PLeft y) with (decEq x y)
    decEq (PLeft x) (PLeft x) | (Yes Refl) = Yes Refl
    decEq (PLeft x) (PLeft y) | (No contra) = No (contra . pLeftInv)
  decEq (PLeft x) (PRight y) = No pLeftRightInv
  decEq (PRight x) (PLeft y) = No (pLeftRightInv . sym)
  decEq (PRight x) (PRight y) with (decEq x y)
    decEq (PRight x) (PRight x) | (Yes Refl) = Yes Refl
    decEq (PRight x) (PRight y) | (No contra) = No (contra . pRightInv)
  decEq (PCat x y) (PCat z w) with (decEq x z)
    decEq (PCat x y) (PCat x w) | (Yes Refl) with (decEq y w)
      decEq (PCat x y) (PCat x y) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (PCat x y) (PCat x w) | (Yes Refl) | (No contra) = No (contra . snd . pCatInv)
    decEq (PCat x y) (PCat z w) | (No contra) = No (contra . fst . pCatInv)
  decEq (PStar []) (PStar []) = Yes Refl
  decEq (PStar []) (PStar (y :: ys)) = No pStarInv1
  decEq (PStar (x :: xs)) (PStar []) = No (pStarInv1 . sym)
  decEq (PStar (x :: xs)) (PStar (y :: ys)) with (decEq x y)
    decEq (PStar (x :: xs)) (PStar (x :: ys)) | (Yes Refl) with (decEq xs ys)
      decEq (PStar (x :: xs)) (PStar (x :: xs)) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (PStar (x :: xs)) (PStar (x :: ys)) | (Yes Refl) | (No contra) 
            = No (contra . snd . pStarInv2)
    decEq (PStar (x :: xs)) (PStar (y :: ys)) | (No contra) = No (contra . fst . pStarInv2)


-- greedy ordering

greedy : ParseTree e -> ParseTree e -> Bool
greedy PEps PEps = False
greedy (PChr _) (PChr _) = False
greedy (PLeft t) (PLeft t') = greedy t t'
greedy (PLeft _) (PRight _) = True
greedy (PRight _) (PLeft _) = False
greedy (PRight t) (PRight t') = greedy t t'
greedy (PCat x y) (PCat z w) with (decEq x z)
  greedy (PCat x y) (PCat x w) | (Yes Refl) = greedy y w
  greedy (PCat x y) (PCat z w) | (No contra) = greedy x z
greedy (PStar []) (PStar []) = True
greedy (PStar []) (PStar (x :: xs)) = False
greedy (PStar (x :: ys)) (PStar []) = ?rhs_1
greedy (PStar (x :: ys)) (PStar (y :: xs)) = ?rhs_2
