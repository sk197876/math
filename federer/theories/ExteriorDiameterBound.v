(** Supporting boundedness for Federer (1969), 2.10.3, pp. 171–172: a set of
    bounded metric diameter has bounded exterior-product gauge. Use the
    product norm inequality of 1.7.5, p. 32, already proved from the
    project's inner and exterior algebra laws. This norm-power upper bound
    supports compact-cover replacement and is not a separately printed claim
    of 2.10.3. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  ExteriorGrading FiniteExteriorPowers ExteriorNorm ExteriorHadamardBound
  ExteriorDiameterUP ExteriorDiameterLaws ExteriorDiameter MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [extended_exterior_diameter_metric_bound]:
    supporting diameter-to-gauge bound for the covering
    alternatives in Federer 2.10.3, pp. 171–172.
    All degrees are allowed in this intermediate bound,
    including degrees greater than the ambient dimension. *)
Theorem extended_exterior_diameter_metric_bound (R : realType) (n m : nat)
    (A : set (R_n R n)) (d : R) : 0<=d ->
  (@extended_metric_diameter R (inner_metric_space (@euclidean_inner_productP R n)) A<=d%:E)%E ->
  (extended_exterior_diameter m A<=(d^+m)%:E)%E.
Proof.
move=> hd hdiam; apply: (exterior_diameter_least_bound
  (extended_exterior_diameter_specification m A)).
- by rewrite lee_fin exprn_ge0.
- move=> a b ha hb.
  have hnorm : exterior_difference_norm a b<=
      \prod_i inner_norm (@euclidean_inner_productP R n) (a i-b i).
    exact (@exterior_product_norm_bound R (real_exterior_two_nonzero R) (R_n R n)
      (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m (fun i => a i-b i)).
  apply: le_trans (lee_tofin hnorm) _; rewrite lee_fin.
  have hp : (\prod_i inner_norm (@euclidean_inner_productP R n) (a i-b i))<=\prod_(i : 'I_m) d.
    apply: ler_prod=> i _; apply/andP; split; first exact: inner_norm_nonnegative.
    have hh := le_trans (@metric_diameter_upper R
      (inner_metric_space (@euclidean_inner_productP R n)) A _
      (@extended_metric_diameter_specification R (inner_metric_space (@euclidean_inner_productP R n)) A)
      (a i) (b i) (ha i) (hb i)) hdiam.
    by move: hh; rewrite lee_fin inner_metric_distanceE.
  by rewrite prodr_const card_ord in hp.
Qed.
