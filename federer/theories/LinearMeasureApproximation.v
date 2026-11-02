(** Federer (1969), 3.2.26(3), p. 262: an
    ambient projection is its own differentiable representative
    on any rectifiable source. Its ordinary linear differential
    is an approximate representative for the restricted source
    measure, without a source-measurability hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormDifferentialLinear
  NormOpenDomainLaws PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  MeasureUP MeasureBasic MeasureRestriction MetricDensities MetricDensityZeroPowerMass
  MeasureApproximateDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [restricted_linear_measure_approximation]: the
    linear representative used when applying 3.2.20 in
    3.2.26(3), p. 262, corrected by erratum p. 5,
    book p. 262 line 14. The agreement contains all
    W, so its complement has zero restricted measure and
    zero metric density at every point. *)
Lemma restricted_linear_measure_approximation (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (phi:set X->\bar R) m (W:set X) (a:X) (L:Hom X Y):
  is_measure phi ->norm_bounded_linear NX NY L ->
  has_measure_approximate_differential NY hNX (measure_restrict phi W) m
    (partial_function_source_restrict W (partial_function_total L)) a L.
Proof.
move=>hPhi hBound.
pose mu:=measure_restrict phi W.
pose f:=partial_function_source_restrict W (partial_function_total L).
pose S:=partial_function_agreement f
  (partial_function_source_restrict setT (partial_function_total L)).
have hMu:=measure_restrict_is_measure hPhi W.
exists setT,L; split.
- exact:(@norm_differential_linear R X Y NX NY hNX hNY setT a L
    (@norm_full_domain_interior R X NX a) hBound).
- have hEmpty:W `&` (~` S)=set0.
    apply/seteqP; split=>x; last by [].
    move=>[hx hn]; exfalso; apply:hn; exists (L x); split; by split.
  have hNull:mu (~` S)=0%E by rewrite /mu /measure_restrict hEmpty (measure_empty hPhi).
  exact:(@null_set_metric_density_zero R (real_norm_metric_space hNX) m mu (~` S) a hMu hNull).
Qed.
