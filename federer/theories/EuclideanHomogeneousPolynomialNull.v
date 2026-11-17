(** Federer (1969), 3.4.7, p. 324: a
    nonzero homogeneous polynomial has null exceptional
    directions for both ambient Lebesgue measure and
    unit-sphere Hausdorff measure. The actual polynomial
    theorem of 2.6.5 and the radial cone argument
    prove the two assertions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  PolynomialFunctions HomogeneousPolynomialFunctions EuclideanLebesgueDimensions HausdorffMeasure
  EuclideanConeSphereNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_homogeneous_polynomial_exceptional_null]:
    both zero-measure assertions for the first nonzero
    homogeneous derivative polynomial in 3.4.7, p. 324.
    This supporting formulation applies to every nonzero
    homogeneous polynomial, without an analytic-source hypothesis. *)
Theorem euclidean_homogeneous_polynomial_exceptional_null (R:realType) n k
    (P:PolynomialFunction (R_n R n.+1) R^o):
  @is_homogeneous_polynomial R (R_n R n.+1) R^o k P ->
  (exists v,P v<>0) ->
  @euclidean_lebesgue_measure R n.+1 [set v|P v = 0] = 0%:E /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n.+1)) n
    [set v|P v = 0 /\inner_norm (@euclidean_inner_productP R n.+1) v = 1] = 0%:E.
Proof.
move=>[F hF] hNonzero.
have hNull:=@euclidean_polynomial_zero_set_null R n.+1 P hNonzero.
split;first exact:hNull.
apply:(@euclidean_null_cone_unit_sphere_null R n [set v|P v = 0]);last exact:hNull.
move=>t ht v hv;change (P (t*:v) = 0).
by rewrite (hF (t*:v)) sform_polynomial_scale_argument -(hF v) hv scaler0.
Qed.
