(** Federer (1969), 2.10.26, p. 190: supporting finite open approximations
    to a compact fibre. Use the open-generator equality from 2.10.2(1), p.
    171, at the final-measure level, choose a near-optimal countable cover,
    and extract a finite subcover. This does not assume fixed-cutoff
    open/all-set equality, which fails in general. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MetricDiameter HausdorffLengthUP HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost
  HausdorffOpenCoverAgreement CaratheodoryLimitUP MetricScaleEnvelopeUP MetricScaleEnvelope
  MetricScaleApproximation CompactFiniteCover NonnegativeSum NonnegativeSumSupport NonnegativeSumImageBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_hausdorff_finite_open_cover_below]:
    supporting finite open covering of a compact fibre
    in 2.10.26, p. 190. Any positive finite
    cutoff and strict extended budget above its
    Hausdorff mass suffice. The compact set can be
    empty; actual open generators are nonempty. *)
Theorem compact_hausdorff_finite_open_cover_below (R : realType) (X : metricType R)
    (A : set X) (k : nat) (d : R) (b : \bar R) :
  compact A -> (0<d)%R -> @hausdorff_measure R X k A<b ->
  exists G : set (set X), finite_set G /\
    (forall S, G S -> open S /\ S!=set0 /\ extended_metric_diameter S<=d%:E) /\
    A `<=` \bigcup_(S in G) S /\ nonnegative_sum G (fun S=>hausdorff_diameter_cost k S)<b.
Proof.
move=> hA hd hbudget.
pose I := @nonempty_open_metric_sets R X.
pose S := fun j : I=>val j.
pose c := fun j : I=>hausdorff_diameter_cost k (S j).
pose nu := metric_scale_envelope S c d%:E.
have hn := metric_scale_envelope_specification S c d%:E.
have hh := @caratheodory_limit_upper R X I S c (@open_hausdorff_measure R X k)
  (@open_hausdorff_measure_specification R X k) A d%:E nu hd hn.
rewrite -hausdorff_open_measure_equality in hh.
have [D [hD [hdiam [hcover hcost]]]] := metric_scale_envelope_approximation hn (le_lt_trans hh hbudget).
have [F hFD hFcover] := @compact_open_finite_cover X I D S A hA
  (fun j _=>(set_valP j).1) hcover.
pose G := S @` [set` F].
have hFsub : [set` F] `<=` D by move=> j hj; exact: set_mem (hFD j hj).
have hG : finite_set G := finite_image S (finite_fset F).
have hGS (T : set X) (hT : G T) : open T /\ T!=set0 /\ extended_metric_diameter T<=d%:E.
  have [j hj <-] := hT; split; first exact: (set_valP j).1.
  split; first exact: (set_valP j).2.
  exact: hdiam j (hFsub j hj).
have hGc : A `<=` \bigcup_(T in G) T.
  move=> x hx; have [j hj hxj] := hFcover x hx; exists (S j)=> //; by exists j.
exists G; split=> //; split=> //; split=> //.
apply: le_lt_trans _ hcost.
apply: le_trans (@nonnegative_sum_image_bound R I [the choiceType of set X]
  [set` F] S (fun T=>hausdorff_diameter_cost k T)
  (fun j _=>hausdorff_diameter_cost_nonnegative k (S j))) _.
exact: nonnegative_sum_subset hFsub.
Qed.
