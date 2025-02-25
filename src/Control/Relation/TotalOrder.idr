||| Irreflexive and trichomotomous relations, and total orders
module Control.Relation.TotalOrder

import Data.Nat
import Decidable.Equality


public export
interface Irreflexive a r | r where
  irrefl : {0 x : a} -> r x x -> Void

||| Alternative version of irreflexivity
public export
irrefl' : Irreflexive a r => {0 x : a} -> {0 y : a} -> r x y -> x = y -> Void
irrefl' p Refl = irrefl p

public export
natIrrefl : LT x x -> Void
natIrrefl (LTESucc y) = natIrrefl y

public export
Irreflexive Nat LT where
  irrefl = natIrrefl


{-
-- Can't get this to work for quantity reasons, which seems suspect
totalOrderAntisymmetry : (Irreflexive a r, Transitive a r) => r x y -> r y x -> Void
totalOrderAntisymmetry p q = irrefl (transitive p q)
-}


public export
data Trichotomy : (r : a -> a -> Type) -> a -> a -> Type where
  LT : {0 x : a} -> {0 y : a} -> r x y -> Trichotomy r x y
  EQ : x = y -> Trichotomy r x y
  GT : {0 x : a} -> {0 y : a} -> r y x -> Trichotomy r x y

public export
interface Trichotomous a r | r where
  trichotomy : (x : a) -> (y : a) -> Trichotomy r x y

public export
trichotomySucc : Trichotomy LT m n -> Trichotomy LT (S m) (S n)
trichotomySucc (LT l) = LT (LTESucc l)
trichotomySucc (EQ e) = EQ (cong S e)
trichotomySucc (GT l) = GT (LTESucc l)

public export
Trichotomous Nat LT where
  trichotomy 0 0 = EQ Refl
  trichotomy 0 (S n) = LT (LTESucc LTEZero)
  trichotomy (S m) 0 = GT (LTESucc LTEZero)
  trichotomy (S m) (S n) = trichotomySucc (trichotomy m n)


public export
succLTE : LTE x y -> LTE x (S y)
succLTE LTEZero = LTEZero
succLTE (LTESucc a) = LTESucc (succLTE a)

public export
precLTE : LTE (S x) y -> LTE x y
precLTE (LTESucc z) = succLTE z

public export
Transitive Nat LT where
  transitive a b = transitive a (precLTE b)


||| Very similar to LinearOrder (in Control.TotalOrder) but based off LT rather than LTE
public export
interface (Irreflexive a r, (Transitive a r, Trichotomous a r)) => TotalOrder a r | r where

public export
TotalOrder Nat LT where


