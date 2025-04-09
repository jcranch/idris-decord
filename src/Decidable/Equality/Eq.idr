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


uncongL : Left x = Left y -> x = y
uncongL Refl = Refl

uncongR : Right x = Right y -> x = y
uncongR Refl = Refl

public export
(EqIsDec a, EqIsDec b) => EqIsDec (Either a b) where
  eqDecides (Left x) (Left y) with (eqDecides x y) | (x == y)
    eqDecides (Left x) (Left y) | No p | False = No (p . uncongL)
    eqDecides (Left x) (Left y) | Yes p | True = Yes (cong Left p)
  eqDecides (Left x) (Right y) = No absurd
  eqDecides (Right x) (Left y) = No absurd
  eqDecides (Right x) (Right y) with (eqDecides x y) | (x == y)
    eqDecides (Right x) (Right y) | No p | False = No (p . uncongR)
    eqDecides (Right x) (Right y) | Yes p | True = Yes (cong Right p)




congFst : (x1,y1) = (x2,y2) -> x1 = x2
congFst Refl = Refl

congSnd : (x1,y1) = (x2,y2) -> y1 = y2
congSnd Refl = Refl

public export
(EqIsDec a, EqIsDec b) => EqIsDec (a, b) where
  eqDecides (x1,y1) (x2,y2) with (eqDecides x1 x2) | (x1 == x2)
    eqDecides (x1,y1) (x2,y2) | No p | False = No (p . congFst)
    eqDecides (x1,y1) (x2,y2) | Yes p | True with (eqDecides y1 y2) | (y1 == y2)
      eqDecides (x1,y1) (x2,y2) | Yes p | True | No q | False = No (q . congSnd)
      eqDecides (x1,y1) (x1,y1) | Yes Refl | True | Yes Refl | True = Yes Refl

{-
-- Fails to find an Eq instance for DPair
public export
(EqIsDec a, (x : a) -> EqIsDec (b x)) => EqIsDec (DPair a b) where
  eqDecides (MkDPair x1 y1) (MkDPair x2 y2) = ?what
-}


nilNeqCons : ([] = a :: as) -> Void
nilNeqCons Refl impossible

consNeqNil : (a :: as = []) -> Void
consNeqNil Refl impossible

uncongHead : {0 as : List x} -> {0 bs : List x} -> (a :: as = b :: bs) -> a = b
uncongHead Refl = Refl

uncongTail : {0 as : List x} -> {0 bs : List x} -> (a :: as = b :: bs) -> as = bs
uncongTail Refl = Refl

public export
EqIsDec a => EqIsDec (List a) where
  eqDecides [] [] = Yes Refl
  eqDecides [] (_ :: _) = No nilNeqCons
  eqDecides (_ :: _) [] = No consNeqNil
  eqDecides (x :: xs) (y :: ys) with (eqDecides x y) | (x == y)
    eqDecides (x :: xs) (y :: ys) | No p | False = No (p . uncongHead)
    eqDecides (x :: xs) (y :: ys) | Yes p | True with (eqDecides xs ys) | (xs == ys)
      eqDecides (x :: xs) (y :: ys) | Yes p | True | No q | False = No (q . uncongTail)
      eqDecides (x :: xs) (x :: xs) | Yes Refl | True | Yes Refl | True = Yes Refl
