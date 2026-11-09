(** Federer (1969), 3.3.14, p. 298: the actual essential
    infinity bound outside a null exceptional set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology NonnegativeExtendedExponentNormUP
  NonnegativeExtendedEssentialBounds MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_essential_almost_bound]: supporting nullity
    of each printed projection exceptional set in Federer 3.3.14,
    p. 298. The actual essential-bound infimum of 2.4.12, p. 86,
    is an almost-everywhere upper bound. Countably many strict
    rational thresholds prove attainment, with infinite values
    retained and no measurability premise on the original input. *)
Lemma structure_essential_almost_bound (R:realType) (X:choiceType)
    (mu:set X->\bar R) (f:X->extended_real_line R) (a: \bar R):
  is_measure mu ->is_nonnegative_extended_exponent_norm mu f +oo a ->
  measure_almost_everywhere mu [set x|f x<=a].
Proof.
move=>hMu hNorm.
pose D:set rat:=[set q|a<(ratr q:R)%:E].
pose N (q:rat):set X:=[set x|(ratr q:R)%:E<f x].
have hNull q:D q ->mu (N q)=0.
  move=>hq; exact:(@nonnegative_extended_essential_strict_upper R X mu hMu f a (ratr q:R)%:E hNorm hq).2.
have hRays:(~` [set x|f x<=a])=\bigcup_(q in D) N q.
  apply/seteqP; split=>x.
  - move=>hNot.
    have hAbove:a<f x.
      rewrite ltNge; apply/negP=>h; exact:hNot h.
    have [q [haq hqf]]:=@extended_rationals_order_dense R a (f x) hAbove.
    exists q; first exact:haq.
    exact:hqf.
  - move=>[q haq hqf] hLe.
    have hAbove:=lt_trans haq hqf.
    by move:hAbove; rewrite ltNge hLe.
rewrite /measure_almost_everywhere hRays.
exact (@measure_null_countable_union R X [the choiceType of (rat:Type)] mu hMu D N (countableP D) hNull).
Qed.
