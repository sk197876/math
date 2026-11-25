(** Federer (1969), 4.1.11, p. 365: the point current
    [u] is the original delta_u and has total one.
    Identify it with the existing scalar-unit point
    multivector current of 4.1.9, p. 363; use the proved
    smooth extension instead of choosing another cutoff. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingZero AlternatingPairing
  CurrentSpaces CurrentEvaluation CurrentCoefficientNorms CurrentDiracDensity CurrentDirac CurrentConstantFields
  CurrentCompactSmoothValue CurrentCompactSmoothAlgebra PointMultivectorCurrentSealed
  PointMultivectorCurrentSupport PointMultivectorCurrentSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDiracSmooth.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Variable c:X.
Hypothesis hc:U c.
Local Notation D := (@dirac_current R h2 n U hU c).
Local Notation unit := (@current_scalar_multivector_unit R n).
Local Notation P := (@PointMultivectorCurrent.value R h2 n 0%N U hU c hc unit).

(** Source for [dirac_current_point_multivector]: delta_c is
    the scalar-unit point current, supporting [c] in
    Federer 4.1.11, p. 365, by 4.1.7, p. 359, and
    4.1.9, p. 363. Equality uses every actual test. *)
Theorem dirac_current_point_multivector:D = P.
Proof.
apply:(@current_values_extensional R h2 n 0%N U hU)=>psi.
rewrite dirac_current_evaluation PointMultivectorCurrent.laws.
by rewrite current_scalar_multivector_unit_pairing.
Qed.

(** Source for [dirac_current_smooth_value]: the original
    smooth extension evaluates a zero-form at c,
    supporting the point-join identities in Federer
    4.1.11, p. 365. Every compactness proof is allowed. *)
Theorem dirac_current_smooth_value
    (hCompact:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n U hU 0%N D))
    (phi:@current_smooth_space R h2 n U hU 0%N):
  @current_compact_smooth_value R h2 n 0%N U hU D hCompact phi=
    zero_form_value (@current_smooth_value R h2 n U hU 0%N phi c).
Proof.
have hPoint:=@point_multivector_current_compact R h2 n 0%N U hU c hc unit.
have hEqual:=@current_compact_smooth_congruence R h2 n 0%N U hU D P hCompact hPoint
  dirac_current_point_multivector.
rewrite hEqual.
have hValue:=@point_multivector_current_smooth_value R h2 n 0%N U hU c hc unit phi.
have hProof:hPoint=(@point_multivector_current_compact R h2 n 0%N U hU c hc unit):=Prop_irrelevance _ _.
rewrite hProof.
exact:(eq_trans hValue (@current_scalar_multivector_unit_pairing R n _)).
Qed.

(** Source for [dirac_current_total]: [c](1)=1, supporting
    the original join and simplex boundary formulas in
    Federer 4.1.11, p. 365. The constant one is used as
    an original smooth form, without a compact-support claim. *)
Theorem dirac_current_total
    (hCompact:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n U hU 0%N D)):
  @current_compact_total R h2 n U hU D hCompact = 1.
Proof.
rewrite /current_compact_total dirac_current_smooth_value
  (@current_constant_form_values R h2 n U hU 0%N _ c hc).
exact:zero_formK.
Qed.
End CurrentDiracSmooth.
