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

## Things still to do

* `Control.Relation.TotalOrder`

    * For usage-related reasons, I can't prove the lemma

        ```
        totalOrderAntisymmetry : (Irreflexive a r, Transitive a r) => r x y -> r y x -> Void
		```

* `Decidable.Equality.Eq`

    * I haven't provided an `EqIsDec` instance for dependent pairs.

* `Decidable.Ordering`

	* There is nothing yet for dependent pairs.

	* I haven't yet proved that `(a, b)` is `DecOrd`. This should be
      possible under suitable hypotheses on `a` and `b`, but it is
      slightly tricky, because the `Ord` instance for `(a, b)` uses
      `Eq`, so we need compatibility between `Eq` and `Ord`.

