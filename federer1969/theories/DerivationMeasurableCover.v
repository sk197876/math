(** The opening Borel almost-cover argument in Federer (1969), 2.9.7, p.
    155: A is contained in Borel B with phi(B minus A)=0. Expand 2.2.3, p.
    61, over the existing countable bounded Borel partition, so infinite
    measurable sets and an empty ambient space are included. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic MeasureFiniteClosure
  BorelRegularMeasureUP BorelRegularSandwich TopologicalBorel CoveringFamilyUP
  BoundedBorelPartitionUP BoundedBorelPartition MeasureDerivationContext.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_measurable_borel_cover]: supporting
    Borel superset in the first proof sentence of
    Federer 2.9.7, p. 155. Only the
    original class-M reference measure and measurability
    of A are used; A may have infinite measure. *)
Theorem derivation_measurable_borel_cover (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (A : set X) :
  is_derivation_measure phi -> measure_measurable phi A ->
  exists B, borel_set B /\ A `<=` B /\ phi (B `\` A)=0.
Proof.
move=> hf hA; have hm := derivation_measure_law hf.
have hr := derivation_measure_borel_regular hf.
have [P hP] := @bounded_borel_partition_exists R X.
pose E n := A `&` P n.
have hE n : exists B, borel_set B /\ E n `<=` B /\ phi (B `\` E n)=0.
  have hPm := @borel_regular_borel_measurable R X phi hm hr (P n) (bounded_borel_partition_borel hP n).
  have hEm := @measure_measurable_intersection R X phi hm A (P n) hA hPm.
  have hEf : phi (E n)< +oo.
    apply: le_lt_trans (@measure_mono R X phi hm (E n) (P n) (fun x hx => hx.2)) _.
    exact: derivation_measure_bounded_finite hf (P n) (bounded_borel_partition_bounded hP n).
  have [D [B [hD [hB [hDE [hEB hz]]]]]] := @borel_regular_finite_sandwich R X phi hm hr (E n) hEm hEf.
  exists B; split=> //; split=> //.
  apply: (@measure_null_subset R X phi hm _ (B `\` D)) hz.
  move=> x [hx hn]; split=> // hdx; apply: hn; exact: hDE x hdx.
pose B n := projT1 (cid (hE n)).
have hB n : borel_set (B n) /\ E n `<=` B n /\ phi (B n `\` E n)=0 := projT2 (cid (hE n)).
exists (\bigcup_n B n); split.
- apply: borel_set_countable_union; first exact: countableP.
  by move=> n _; exact: (hB n).1.
- split.
  + move=> x hx.
    have hcover : (\bigcup_n P n) x by rewrite (bounded_borel_partition_union hP).
    have [n _ hn] := hcover; exists n=> //; apply: (hB n).2.1; by split.
  + have hz : phi (\bigcup_n (B n `\` E n))=0.
      apply: (@measure_null_countable_union R X _ phi hm setT (fun n => B n `\` E n) (countableP _)).
      by move=> n _; exact: (hB n).2.2.
    apply: (@measure_null_subset R X phi hm _ (\bigcup_n (B n `\` E n))) hz.
    move=> x [[n _ hx] hn]; exists n=> //; split=> //; by move=> [ha _]; apply: hn.
Qed.
