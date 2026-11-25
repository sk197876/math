(** Federer (1969), 2.10.34, printed p. 197: Gross measure is at most
    exterior-diameter measure. The pointwise projected-volume cost
    comparison is already proved. Use the compact-cover specification of
    2.10.3, p. 172, so each exterior generator is also an eligible Borel
    generator for Gross measure. This retains arbitrary target sets,
    including empty sets and infinite measure. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric ProjectedVolumeGauge ProjectionMeasureUP ProjectionMeasure
  ExteriorMeasureGauge ExteriorMeasureUP ExteriorMeasure ExteriorCompactCoverUP ExteriorCompactCoverAgreement
  ProjectedExteriorGaugeBound CaratheodoryFamilyReplacement BorelCoverCostUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [gross_compact_exterior_comparison]: supporting
    independent-specification version of 2.10.34,
    p. 197. Compact exterior generators
    are Borel, so no measurable-hull choice
    or target regularity hypothesis is needed. *)
Theorem gross_compact_exterior_comparison (R : realType) (n m : nat)
    (mu nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :
  (m<=n)%N -> is_gross_measure m mu -> is_compact_exterior_diameter_measure m nu ->
  forall A, (mu A<=nu A)%E.
Proof.
move=> hmn hm hn A.
apply: (@caratheodory_family_replacement R (inner_metric_space (@euclidean_inner_productP R n))
  (@nonempty_compact_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
  (@borel_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
  (fun j=>val j) (fun j=>val j) (fun j=>exterior_diameter_cost m (val j))
  (fun j=>projected_volume_gauge m (val j)) nu mu hn hm _ _ A).
- move=> j; exact: projected_volume_gauge_nonnegative hmn.
- move=> j.
  have hb : borel_set (val j).
    apply: closed_borel_set.
    exact: compact_closed (@metric_hausdorff R (inner_metric_space (@euclidean_inner_productP R n))) (set_valP j).1.
  pose k : @borel_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) :=
    @exist _ (fun B=>B \in @borel_set (inner_metric_space (@euclidean_inner_productP R n))) (val j) (mem_set hb).
  exists k; split; first by move=> x hx.
  split; first exact: lexx.
  exact: projected_volume_gauge_exterior_bound (set_valP j).2.
Qed.

(** Source for [federer_2_10_34]: direct corollary
    2.10.34, p. 197: G^m(A)<=T^m(A)
    for arbitrary A in R^n. The
    m<=n convention is inherited from Gross
    measure in 2.10.4, p. 172;
    its supporting natural-degree interface also allows zero. *)
Theorem federer_2_10_34 (R : realType) (n m : nat) :
  (m<=n)%N -> forall A, (@gross_measure R n m A<=@exterior_diameter_measure R n m A)%E.
Proof.
move=> hmn; exact: (@gross_compact_exterior_comparison R n m _ _ hmn
  (gross_measure_specification R n m) (exterior_measure_compact_cover_specification R n m)).
Qed.
