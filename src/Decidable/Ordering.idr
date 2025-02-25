module Decidable.Ordering

import Control.Relation.TotalOrder
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Eq


public export
data OrdDecides : (a -> a -> Type) -> (x : a) -> (y : a) -> Ordering -> Type where
  LT : {0 r : a -> a -> Type} -> r x y -> OrdDecides r x y LT
  EQ : {0 r : a -> a -> Type} -> x = y -> OrdDecides r x y EQ
  GT : {0 r : a -> a -> Type} -> r y x -> OrdDecides r x y GT

public export
interface (TotalOrder a r, Ord a) => DecOrd a (r : a -> a -> Type) where
  decOrd : (x : a) -> (y : a) -> OrdDecides r x y (compare x y)

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



public export
ordDecidesEq : (Ord a, Irreflexive a r) => {x : a} -> {y : a} -> OrdDecides r x y (compare x y) -> Dec (x = y)
ordDecidesEq d with (compare x y)
  ordDecidesEq (LT p) | LT = No (irrefl' p)
  ordDecidesEq (EQ p) | EQ = Yes p
  ordDecidesEq (GT p) | GT = No (\e => irrefl' p (sym e))
