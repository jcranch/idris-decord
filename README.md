# decord

This Idris library does several things:

* `Control.Relation.TotalOrder` axiomatises "less than" relationships in
  a similar way to how the standard library axiomatises "less than or
  equal to".

* `Decidable.Equality.Eq` contains the means to express that an `Eq`
  instance is compatible with propositional equality.

* `Decidable.EqOrd` contains the means to express that `Eq` and `Ord`
  instances are compatible.

* `Decidable.Ordering` contains a framework for decidable orderings,
  compatible with `Ord` instances.
