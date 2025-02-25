||| Provides a type for proving compatibility between Eq and Ord
module Decidable.EqOrd


||| Compatibility between Eq and Ord
public export
data EqOrdCompat : Bool -> Ordering -> Type where
  LT : EqOrdCompat False LT
  GT : EqOrdCompat False GT
  EQ : EqOrdCompat True EQ


||| Types with compatible Eq and Ord instances
public export
interface Ord x => OrdCompatible x where
  eqOrdCompat : (a : x) -> (b : x) -> EqOrdCompat (a == b) (compare a b)

public export
OrdCompatible () where
  eqOrdCompat () () = EQ

public export
OrdCompatible Bool where
  eqOrdCompat True True = EQ
  eqOrdCompat False False = EQ
  eqOrdCompat True False = GT
  eqOrdCompat False True = LT

public export
eqOrdCompatSucc : EqOrdCompat (a == b) (compare a b) -> EqOrdCompat (S a == S b) (compare (S a) (S b))
eqOrdCompatSucc {a} {b} c with 0 (a == b) | 0 (compare a b)
  eqOrdCompatSucc EQ | True | EQ = EQ
  eqOrdCompatSucc GT | False | GT = GT
  eqOrdCompatSucc LT | False | LT = LT

public export
OrdCompatible Nat where
  eqOrdCompat 0 0 = EQ
  eqOrdCompat (S m) 0 = GT
  eqOrdCompat 0 (S n) = LT
  eqOrdCompat (S m) (S n) = eqOrdCompatSucc (eqOrdCompat m n)
