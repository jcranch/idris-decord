||| A form of decidable equality compatible with Eq
module Decidable.Equality.Eq

import Data.Nat
import Decidable.Equality


||| Compatibility between a boolean and a proposition
public export
data Decides : Bool -> Type -> Type where
  Yes : p -> Decides True p
  No : (p -> Void) -> Decides False p


||| Decidable equality compatible with an Eq instance
public export
interface Eq x => EqIsDec x where
  eqDecides : (a : x) -> (b : x) -> Decides (a == b) (a = b)


public export
decidesToDec : Decides t p -> Dec p
decidesToDec (Yes x) = Yes x
decidesToDec (No x) = No x


public export
EqIsDec () where
  eqDecides () () = Yes Refl

public export
EqIsDec Bool where
  eqDecides True True = Yes Refl
  eqDecides False False = Yes Refl
  eqDecides True False = No absurd
  eqDecides False True = No absurd


public export
eqPrec : S l = S r -> l = r
eqPrec Refl = Refl

public export
neSucc : (l = r -> Void) -> S l = S r -> Void
neSucc f p = f (eqPrec p)

public export
decSucc : Decides (m == n) (m = n) -> Decides (S m == S n) (S m = S n)
decSucc d with 0 (m == n)
  decSucc (Yes r) | True = Yes (cong S r)
  decSucc (No r) | False = No (neSucc r)


public export
EqIsDec Nat where
  eqDecides 0 0 = Yes Refl
  eqDecides (S m) 0 = No absurd
  eqDecides 0 (S n) = No absurd
  eqDecides (S m) (S n) = decSucc (eqDecides m n)
