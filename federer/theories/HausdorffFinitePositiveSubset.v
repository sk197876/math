(** Federer (1969), 2.10.47, pp. 204–205: a compact Euclidean set of
    positive Hausdorff measure contains a compact subset of finite positive
    measure. The degree-zero and ambient-dimension induction cases are
    included; no null-section or root-cube hypothesis remains. Natural
    degrees use the existing alpha(m) normalisation exactly. The real-degree
    theorem is proved for every positive coefficient, without assuming the
    separate Euler-Gamma construction pending in 2.10.2. No relevant
    correction occurs in the local Federer erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanPositiveCompactSubset RealPowerZeroCompactSubset RealPowerNaturalHausdorff
  MetricRealPowerMeasureUP HausdorffDiameterCost HausdorffMeasureUP HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_47_real_power]: theorem 2.10.47,
    pp. 204–205, for every nonnegative real degree
    and explicit positive coefficient. The proof follows
    Federer's induction and compact dyadic pruning. *)
Theorem federer_2_10_47_real_power (R : realType) n c p
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_metric_real_power_measure c p mu -> (0<c)%R -> (0<=p)%R -> compact A -> 0<mu A ->
  exists B, [/\ compact B, B `<=` A, 0<mu B & mu B< +oo].
Proof.
move=> hmu hc hp hA hpos; case: (eqVneq p 0%R)=> [he|hne].
- rewrite he in hmu; exact: real_power_zero_compact_subset hmu hc hpos.
- have hp' : (0<p)%R by rewrite lt_neqAle eq_sym hne hp.
  exact: metric_real_power_compact_finite_positive_subset hmu hc hp' hA hpos.
Qed.

(** Source for [federer_2_10_47_abstract]: theorem 2.10.47,
    pp. 204–205, through the abstract Hausdorff
    specification with the printed natural-degree coefficient. *)
Theorem federer_2_10_47_abstract (R : realType) n m
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_hausdorff_measure m mu -> compact A -> 0<mu A ->
  exists B, [/\ compact B, B `<=` A, 0<mu B & mu B< +oo].
Proof.
move=> hmu hA hpos.
exact (@federer_2_10_47_real_power R n (hausdorff_normalisation R m) m%:R mu A
  (@hausdorff_natural_real_power_laws R (inner_metric_space (@euclidean_inner_productP R n)) m mu hmu)
  (hausdorff_normalisation_positive R m) (ltac:(by rewrite ler0n)) hA hpos).
Qed.

(** Source for [federer_2_10_47]: theorem 2.10.47,
    pp. 204–205, for the public opaque Hausdorff
    measure, including m=0 and ambient dimension zero. *)
Theorem federer_2_10_47 (R : realType) n m
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  compact A -> 0<hausdorff_measure m A ->
  exists B, [/\ compact B, B `<=` A, 0<hausdorff_measure m B & hausdorff_measure m B< +oo].
Proof. exact: federer_2_10_47_abstract (hausdorff_measure_specification _ m). Qed.
