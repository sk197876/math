(** Federer (1969), 2.10.33, printed p. 197: the isodiametric inequality,
    deduced from 2.10.32 and the exterior-product norm estimate of 1.7.5, p.
    32. The proof uses only the abstract diameter and exterior-supremum
    specifications. It includes infinite diameter and natural dimension
    zero. No relevant correction in Federer's working erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric ExteriorHadamardBound
  ExteriorDiameterUP ExteriorDiameterLaws ExteriorDiameter ExteriorDiameterBound
  MetricDiameterUP MetricDiameter ExteriorMeasureGauge HausdorffDiameterCost
  EuclideanLebesgueDimensions EuclideanExteriorVolumeTheorem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [exterior_diameter_metric_power_bound]: supporting
    extended-valued form of the product estimate
    displayed in the proof of 2.10.33,
    p. 197. Any natural exterior degree is
    allowed, even above the ambient dimension. *)
Lemma exterior_diameter_metric_power_bound (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (extended_exterior_diameter m S <= (extended_metric_diameter S)^+m)%E.
Proof.
have hnon := metric_diameter_nonnegative (extended_metric_diameter_specification S).
case hd: (extended_metric_diameter S) hnon=> [d| |] hnon.
- rewrite lee_fin in hnon; rewrite -EFin_expe.
  apply: (@extended_exterior_diameter_metric_bound R n m S d hnon).
  by rewrite hd.
- case: m=> [|m]; last by rewrite expeS gt0_mulye ?expe_gt0 // leey.
  rewrite expe0; apply: (exterior_diameter_least_bound (extended_exterior_diameter_specification 0 S)).
  + by rewrite lee_fin ler01.
  + move=> a b ha hb; rewrite lee_fin.
    have hh := @exterior_product_norm_bound R (real_exterior_two_nonzero R) (R_n R n)
      (@euclidean_inner_product R n) (@euclidean_inner_productP R n) 0 (fun i => a i-b i).
    by rewrite big_ord0 in hh.
- by rewrite leeNy_eq in hnon.
Qed.

(** Source for [lebesgue_isodiametric_bound]: direct corollary
    2.10.33, p. 197, with its right-hand
    side expressed by the normalised diameter
    cost of 2.10.2, p. 171. The
    nonempty source need not be measurable or bounded. *)
Theorem lebesgue_isodiametric_bound (R : realType) (n : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  S !=set0 -> (euclidean_lebesgue_measure n S <= hausdorff_diameter_cost n S)%E.
Proof.
move=> hS; apply: le_trans (@lebesgue_top_exterior_cost_bound R n S hS) _.
rewrite /exterior_diameter_cost /hausdorff_diameter_cost /hausdorff_power_cost.
apply: lee_wpmul2l; last exact: exterior_diameter_metric_power_bound.
rewrite lee_fin; exact: ltW (hausdorff_normalisation_positive R n).
Qed.

(** Source for [federer_2_10_33]: direct printed formula
    of the isodiametric corollary 2.10.33,
    p. 197. The coefficient is alpha(n)/2^n
    and the diameter is raised to n.
    Extended powers use infinity^0=1 in dimension zero. *)
Theorem federer_2_10_33 (R : realType) (n : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  S !=set0 -> (euclidean_lebesgue_measure n S <=
    (hausdorff_normalisation R n)%:E*(extended_metric_diameter S)^+n)%E.
Proof. exact: lebesgue_isodiametric_bound. Qed.
