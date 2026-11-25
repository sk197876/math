(** Federer (1969), 2.9.17, p. 162: the zero-or-infinite upper radial
    derivative on a numerator-null measurable set. The May 1987 erratum, p.
    3, book p. 162 lines 24–25, corrects the closed-ball typography in the
    covering estimate. they do not state this theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic MeasureDerivationContext
  DerivationCountableMeasurability CountablyMeasurableUP CountablyMeasurableSequences
  BorelRegularApproximation ClosedApproximationUP ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.


(** Source for [derivation_measurable_closed_almost_cover]: supporting
    reduction to a closed target in Federer 2.9.17, p. 162, citing 2.2.3. A
    class-M measurable set is covered up to a null remainder by countably
    many closed subsets, without finite total mass. two natural indices
    avoid choosing an enumeration. *)
Theorem derivation_measurable_closed_almost_cover (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (T : set X) :
  is_derivation_measure phi -> measure_measurable phi T ->
  exists C : (nat*nat)%type -> set X,
    (forall j, closed (C j) /\ C j `<=` T) /\
    phi (T `\` \bigcup_j C j)=0.
Proof.
move=> hphi hT; have hm := derivation_measure_law hphi.
have hr := derivation_measure_borel_regular hphi.
have hcnt := @derivation_measure_measurable_countably_measurable R X phi T hphi hT.
have [A [hcover hA]] := (proj1 (@countably_measurable_sequence_iff R X phi hm T)) hcnt.
have hex (p : (nat*nat)%type) := @borel_regular_closed_approximation R X phi hm hr
  (A p.1) (hA p.1).1 (hA p.1).2 (((p.2.+1)%:R)^-1)%R
  (ltac:(by rewrite invr_gt0 ltr0n)).
pose C (p : (nat*nat)%type) := projT1 (cid (hex p)).
have hC p : closed (C p) /\ C p `<=` A p.1 /\
    phi (A p.1 `\` C p)<(((p.2.+1)%:R)^-1)%R%:E.
  exact: projT2 (cid (hex p)).
pose S := \bigcup_p C p.
have hzero n : phi (A n `\` S)=0.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  apply: (@extended_real_reciprocal_upper_bound R _ 0%R)=> k; rewrite add0r.
  apply: le_trans _ (ltW (hC (n,k)).2.2).
  apply: (@measure_mono R X phi hm)=> x [hx hn]; split=> // hc.
  apply: hn; by exists (n,k).
exists C; split.
- move=> p; split; first exact: (hC p).1.
  move=> x hx; rewrite hcover; exists p.1=> //; exact: (hC p).2.1 x hx.
- apply: (@measure_null_subset R X phi hm (T `\` S) (\bigcup_n (A n `\` S))).
  + move=> x [hx hn]; rewrite hcover in hx.
    have [n _ ha] := hx; exists n=> //; by split.
  + apply: (@measure_null_countable_union R X nat phi hm setT _ (countableP _)).
    by move=> n _; exact: hzero n.
Qed.
