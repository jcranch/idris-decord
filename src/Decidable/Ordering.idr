module Decidable.Ordering

import Control.Relation.TotalOrder
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Eq
import Decidable.EqOrd


public export
data OrdDecides : (0 r : a -> a -> Type) -> (x : a) -> (y : a) -> Ordering -> Type where
  LT : {0 r : a -> a -> Type} -> r x y -> OrdDecides r x y LT
  EQ : {0 r : a -> a -> Type} -> x = y -> OrdDecides r x y EQ
  GT : {0 r : a -> a -> Type} -> r y x -> OrdDecides r x y GT

public export
interface (TotalOrder a r, Ord a) => DecOrd a (0 r : a -> a -> Type) where
  decOrd : (x : a) -> (y : a) -> OrdDecides r x y (compare x y)


public export
ordDecidesEq : (Ord a, Irreflexive a r) => {x : a} -> {y : a} -> OrdDecides r x y (compare x y) -> Dec (x = y)
ordDecidesEq d with (compare x y)
  ordDecidesEq (LT p) | LT = No (irrefl' p)
  ordDecidesEq (EQ p) | EQ = Yes p
  ordDecidesEq (GT p) | GT = No (\e => irrefl' p (sym e))


public export
data BoolOrder : Bool -> Bool -> Type where
  FalseTrue : BoolOrder False True

public export
Irreflexive Bool BoolOrder where
  irrefl FalseTrue impossible

public export
Trichotomous Bool BoolOrder where
  trichotomy False False = EQ Refl
  trichotomy False True = LT FalseTrue
  trichotomy True False = GT FalseTrue
  trichotomy True True = EQ Refl

public export
Transitive Bool BoolOrder where
  transitive FalseTrue FalseTrue impossible

public export
TotalOrder Bool BoolOrder where

public export
DecOrd Bool BoolOrder where
  decOrd False True = LT FalseTrue
  decOrd True False = GT FalseTrue
  decOrd False False = EQ Refl
  decOrd True True = EQ Refl

public export
decOrdNatSucc : OrdDecides LT m n (compare m n) -> OrdDecides LT (S m) (S n) (compare (S m) (S n))
decOrdNatSucc {m} {n} c with 0 (compare m n)
  decOrdNatSucc (LT p) | LT = LT (LTESucc p)
  decOrdNatSucc (EQ q) | EQ = EQ (cong S q)
  decOrdNatSucc (GT r) | GT = GT (LTESucc r)

public export
DecOrd Nat LT where
  decOrd 0 0 = EQ Refl
  decOrd 0 (S n) = LT (LTESucc LTEZero)
  decOrd (S m) 0 = GT (LTESucc LTEZero)
  decOrd (S m) (S n) = decOrdNatSucc (decOrd m n)


data EitherOrder : {0 a : Type} -> {0 b : Type} -> (a -> a -> Type) -> (b -> b -> Type) -> Either a b -> Either a b -> Type where
  LL : {0 x : a} -> {0 y : a} -> r x y -> EitherOrder r s (Left x) (Left y)
  LR : EitherOrder r s (Left x) (Right y)
  RR : {0 x : b} -> {0 y : b} -> s x y -> EitherOrder r s (Right x) (Right y)

(Irreflexive a r, Irreflexive b s) => Irreflexive (Either a b) (EitherOrder r s) where
  irrefl (LL e) = irrefl e
  irrefl (RR e) = irrefl e

(Trichotomous a r, Trichotomous b s) => Trichotomous (Either a b) (EitherOrder r s) where
  trichotomy (Left x) (Left y) with (trichotomy {r = r} x y)
    trichotomy (Left x) (Left y) | LT e = LT (LL e)
    trichotomy (Left x) (Left x) | EQ Refl = EQ Refl
    trichotomy (Left x) (Left y) | GT e = GT (LL e)
  trichotomy (Left x) (Right y) = LT LR
  trichotomy (Right x) (Left y) = GT LR
  trichotomy (Right x) (Right y) with (trichotomy {r = s} x y)
    trichotomy (Right x) (Right y) | (LT e) = LT (RR e)
    trichotomy (Right x) (Right x) | (EQ Refl) = EQ Refl
    trichotomy (Right x) (Right y) | (GT e) = GT (RR e)

(Transitive a r, Transitive b s) => Transitive (Either a b) (EitherOrder r s) where
  transitive (LL u) (LL v) = LL (transitive u v)
  transitive (LL _) LR = LR
  transitive LR (RR _) = LR
  transitive (RR u) (RR v) = RR (transitive u v)

(TotalOrder a r, TotalOrder b s) => TotalOrder (Either a b) (EitherOrder r s) where

(DecOrd a r, DecOrd b s) => DecOrd (Either a b) (EitherOrder r s) where
  decOrd (Left x) (Left y) with (decOrd {r = r} x y) | (compare x y)
    decOrd (Left x) (Left y) | (LT p) | LT = LT (LL p)
    decOrd (Left x) (Left y) | (EQ e) | EQ = EQ (cong Left e)
    decOrd (Left x) (Left y) | (GT p) | GT = GT (LL p)
  decOrd (Left x) (Right y) = LT LR
  decOrd (Right x) (Left y) = GT LR
  decOrd (Right x) (Right y) with (decOrd {r = s} x y) | (compare x y)
    decOrd (Right x) (Right y) | (LT p) | LT = LT (RR p)
    decOrd (Right x) (Right y) | (EQ e) | EQ = EQ (cong Right e)
    decOrd (Right x) (Right y) | (GT p) | GT = GT (RR p)


data PairOrder : {0 a : Type} -> {0 b : Type} -> (a -> a -> Type) -> (b -> b -> Type) -> (a, b) -> (a, b) -> Type where
  OnFst : {0 y1 : b} -> {0 y2 : b} -> r x1 x2 -> PairOrder r s (x1,y1) (x2,y2)
  OnSnd : x1 = x2 -> s y1 y2 -> PairOrder r s (x1,y1) (x2,y2)

(Irreflexive a r, Irreflexive b s) => Irreflexive (a, b) (PairOrder r s) where
  irrefl (OnFst p) = irrefl p
  irrefl (OnSnd _ p) = irrefl p

(Trichotomous a r, Trichotomous b s) => Trichotomous (a, b) (PairOrder r s) where
  trichotomy (x1,y1) (x2,y2) with (trichotomy {r = r} x1 x2)
    trichotomy (x1,y1) (x2,y2) | (LT p) = LT (OnFst p)
    trichotomy (x1,y1) (x2,y2) | (GT p) = GT (OnFst p)
    trichotomy (x1,y1) (x2,y2) | (EQ e) with (trichotomy {r = s} y1 y2)
      trichotomy (x1,y1) (x2,y2) | (EQ e) | (LT p) = LT (OnSnd e p)
      trichotomy (x1,y1) (x2,y2) | (EQ e) | (GT p) = GT (OnSnd (sym e) p)
      trichotomy (x1,y1) (x1,y1) | (EQ Refl) | (EQ Refl) = EQ Refl

(Transitive a r, Transitive b s) => Transitive (a, b) (PairOrder r s) where
  transitive (OnFst p) (OnFst q) = OnFst (transitive p q)
  transitive (OnFst p) (OnSnd Refl _) = OnFst p
  transitive (OnSnd Refl _) (OnFst q) = OnFst q
  transitive (OnSnd Refl p) (OnSnd Refl q) = OnSnd Refl (transitive p q)

(TotalOrder a r, TotalOrder b s) => TotalOrder (a, b) (PairOrder r s) where

{-
(OrdCompatible a, DecOrd a r, DecOrd b s) => DecOrd (a, b) (PairOrder r s) where
  decOrd (x1,y1) (x2,y2) with (decOrd {r = r} x1 x2) | (eqOrdCompat x1 x2) | (compare x1 x2) | (x1 == x2)
    decOrd (x1,y1) (x2,y2) | DecOrd.LT p | EqOrdCompat.LT | Compare.LT | False = ?what1
    decOrd (x1,y1) (x2,y2) | DecOrd.EQ e | EqOrdCompat.EQ | Compare.EQ | True = ?what2
    decOrd (x1,y1) (x2,y2) | DecOrd.GT p | EqOrdCompat.GT | Compare.GT | False = ?what3
-}


data Lexicographic : (r : a -> a -> Type) -> List a -> List a -> Type where
  CmpNil : Lexicographic r [] (y :: ys)
  CmpNow : {0 xs : List a} -> {0 ys : List a} -> r x y -> Lexicographic r (x :: xs) (y :: ys)
  CmpLater : x = y -> Lexicographic r xs ys -> Lexicographic r (x :: xs) (y :: ys)

(Irreflexive a r) => Irreflexive (List a) (Lexicographic r) where
  irrefl (CmpNow p) = irrefl p
  irrefl (CmpLater _ p) = irrefl p

(Trichotomous a r) => Trichotomous (List a) (Lexicographic r) where
  trichotomy [] [] = EQ Refl
  trichotomy [] (_ :: _) = LT CmpNil
  trichotomy (_ :: _) [] = GT CmpNil
  trichotomy (x :: xs) (y :: ys) with (trichotomy {r} x y)
    trichotomy (x :: xs) (y :: ys) | (LT p) = LT (CmpNow p)
    trichotomy (x :: xs) (y :: ys) | (GT p) = GT (CmpNow p)
    trichotomy (x :: xs) (y :: ys) | (EQ e) with (trichotomy {r = Lexicographic r} xs ys)
      trichotomy (x :: xs) (y :: ys) | (EQ e) | (LT p) = LT (CmpLater e p)
      trichotomy (x :: xs) (y :: ys) | (EQ e) | (GT p) = GT (CmpLater (sym e) p)
      trichotomy (x :: xs) (x :: xs) | (EQ Refl) | (EQ Refl) = EQ Refl

(Transitive a r) => Transitive (List a) (Lexicographic r) where
  transitive CmpNil (CmpNow _) = CmpNil
  transitive CmpNil (CmpLater _ _) = CmpNil
  transitive (CmpNow p) (CmpNow q) = CmpNow (transitive p q)
  transitive (CmpNow p) (CmpLater Refl _) = CmpNow p
  transitive (CmpLater Refl _) (CmpNow q) = CmpNow q
  transitive (CmpLater Refl p) (CmpLater Refl q) = CmpLater Refl (transitive p q)

(TotalOrder a r) => TotalOrder (List a) (Lexicographic r) where

(DecOrd a r) => DecOrd (List a) (Lexicographic r) where
  decOrd [] [] = EQ Refl
  decOrd [] (y :: ys) = LT CmpNil
  decOrd (x :: xs) [] = GT CmpNil
  decOrd (x :: xs) (y :: ys) with (decOrd {r = r} x y) | (compare x y)
    decOrd (x :: xs) (y :: ys) | (LT p) | LT = LT (CmpNow p)
    decOrd (x :: xs) (y :: ys) | (GT p) | GT = GT (CmpNow p)
    decOrd (x :: xs) (y :: ys) | (EQ e) | EQ with (decOrd {r = Lexicographic r} xs ys) | (compare xs ys)
      decOrd (x :: xs) (y :: ys) | (EQ e) | EQ | (LT p) | LT = LT (CmpLater e p)
      decOrd (x :: xs) (y :: ys) | (EQ e) | EQ | (GT p) | GT = GT (CmpLater (sym e) p)
      decOrd (x :: xs) (y :: ys) | (EQ e) | EQ | (EQ f) | EQ = EQ (cong2 (::) e f)
