(** Federer (1969), 2.3.6, p. 77, first corollary: apply Lusin on a
    countable finite-measure cover, with errors tending to zero. A two-index
    countable family retains the exact cover without an arbitrary pairing
    convention. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialContinuityUP MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic CountablyMeasurableUP CountablyMeasurableSequences
  ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [lusin_closed_exhaustion]: supporting almost-full
    closed continuity cover in Federer 2.3.6, p. 77. The
    source need only be countably measurable, as in 2.3.4. *)
Theorem lusin_closed_exhaustion (R : realType) (X Y : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X Y) :
  measure_countably_measurable mu setT ->
  (forall A, measure_measurable mu A -> mu A < +oo -> forall e : R, (0 < e)%R ->
    exists C, closed C /\ C `<=` A /\ mu (A `\` C) < e%:E /\ partial_function_continuous_on C f) ->
  exists C : nat * nat -> set X, (forall j, closed (C j)) /\
    (forall j, partial_function_continuous_on (C j) f) /\
    measure_almost_everywhere mu (\bigcup_j C j).
Proof.
move=> hcnt happ.
have [A [hcover hA]] := (proj1 (@countably_measurable_sequence_iff R X mu hm setT)) hcnt.
have hex (p : nat * nat) := happ (A p.1) (hA p.1).1 (hA p.1).2
  (((p.2.+1)%:R)^-1)%R (ltac:(by rewrite invr_gt0 ltr0n)).
pose C p := projT1 (cid (hex p)).
have hC p : closed (C p) /\ C p `<=` A p.1 /\
    mu (A p.1 `\` C p) < (((p.2.+1)%:R)^-1)%:E /\ partial_function_continuous_on (C p) f.
  exact: projT2 (cid (hex p)).
pose S := \bigcup_p C p.
have hzero n : mu (A n `\` S) = 0.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  apply: (@extended_real_reciprocal_upper_bound R _ 0)=> k; rewrite add0r.
  apply: le_trans _ (ltW (hC (n,k)).2.2.1).
  apply: (@measure_mono R X mu hm)=> x [hx hn]; split=> // hc.
  apply: hn; by exists (n,k).
exists C; split; first by move=> p; exact: (hC p).1.
split; first by move=> p; exact: (hC p).2.2.2.
apply: (@measure_null_subset R X mu hm (~` S) (\bigcup_n (A n `\` S))).
- move=> x hn; have hx : (\bigcup_n A n) x by rewrite -hcover.
  have [n _ ha] := hx; exists n; first exact Logic.I; by split.
- apply: (@measure_null_countable_union R X nat mu hm setT _ (countableP _)).
  by move=> n _; exact: hzero n.
Qed.
