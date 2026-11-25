(** Federer (1969), 3.4.10, p. 337:
    a zero-dimensional analytic set has no
    nonregular part. This states the endpoint
    without extending Hausdorff measure to negative degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness AnalyticVarietyGermUP
  AnalyticSetLocalDepth AnalyticSetDimension BoundedNaturalSupremumUP
  AnalyticRegularLocusUP AnalyticRegularLocusSealed AnalyticCentreZeroRegular.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_10_zero_regular]: the
    dimension-zero endpoint of the regular-part
    assertion of 3.4.10, p. 337.
    The actual opaque regular part equals S. *)
Theorem federer_3_4_10_zero_regular (R:realType) n (U S:set (R_n R n)):
  let hB:=@euclidean_inner_productP R n in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @open T U ->S `<=` U ->
  @is_analytic_set_in R (R_n R n) (inner_norm hB) hNX U S ->
  @analytic_set_dimension R n S=0%N ->
  @AnalyticRegularLocus.value R n 0 U S=S.
Proof.
move=>hB hNX T hU hSU hAnalytic hDimension.
apply/seteqP;split.
- move=>a /(AnalyticRegularLocus.laws)=>h;exact:h.1.
- move=>a haS.
  have hBound:(@analytic_set_local_depth R n S a<=0)%N.
    rewrite -hDimension.
    exact:(@bounded_natural_supremum_upper (R_n R n) S
      (@analytic_set_local_depth R n S) (@analytic_set_dimension R n S)
      (@analytic_set_dimension_laws R n S) a haS).
  exact:(@analytic_centre_zero_regular R n U S
    (@AnalyticRegularLocus.value R n 0 U S) a hU (hSU a haS)
    (hAnalytic a (hSU a haS)) hBound (@AnalyticRegularLocus.laws R n 0 U S) haS).
Qed.
