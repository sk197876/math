(** Federer (1969), 4.1.8, p. 362: the original
    oriented segment has boundary delta_v-delta_u. The
    actual scalar interval fundamental theorem proves the
    all-test identity; no boundary formula is assumed
    in the independent segment-current specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingZero CurrentCoefficientNorms
  CurrentSpaces CurrentEvaluation CurrentPointEvaluation CurrentBoundary CurrentTestExteriorDerivative
  CurrentDirac CurrentSegmentMapUP OrientedSegmentCurrentUP OrientedSegmentCurrentSealed
  CurrentOpenScalarAffineIntegral MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section OrientedSegmentCurrentBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Variable A:set X.
Hypothesis hA:forall x,A x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) A x.
Variables u v:X.
Hypothesis hSegment:@is_current_segment_domain R n A u v.
Local Notation S := (@OrientedSegmentCurrent.value R h2 n A hA u v hSegment).
Local Notation delta := (@dirac_current R h2 n A hA).

(** Source for [oriented_segment_current_boundary]:
    boundary [u,v]=delta_v-delta_u, the original printed
    segment identity in Federer 4.1.8, p. 362. This
    retains degenerate segments and zero-dimensional
    ambient spaces in every original containing open set. *)
Theorem oriented_segment_current_boundary:
  @current_boundary R h2 n 0%N A hA S=delta v-delta u.
Proof.
apply:(@current_values_extensional R h2 n 0%N A hA)=>psi.
rewrite current_boundary_evaluation.
have hAction:=@OrientedSegmentCurrent.laws R h2 n A hA u v hSegment
  (@current_test_exterior_derivative R h2 n 0%N A hA psi).
have hFTC:=@current_open_scalar_affine_integral R h2 n A hA psi u v.
have hValue:=EFin_inj (measure_integral_unique hAction hFTC).
have hDifference:@current_value R h2 n A hA 0%N (delta v-delta u) psi=
    zero_form_value (@current_test_value R h2 n A hA 0%N psi v)-
    zero_form_value (@current_test_value R h2 n A hA 0%N psi u).
  change (@current_point_evaluation R h2 n 0%N A hA psi (delta v-delta u)=
    zero_form_value (@current_test_value R h2 n A hA 0%N psi v)-
    zero_form_value (@current_test_value R h2 n A hA 0%N psi u)).
  rewrite linearB.
  change (@current_value R h2 n A hA 0%N (delta v) psi-
    @current_value R h2 n A hA 0%N (delta u) psi=
    zero_form_value (@current_test_value R h2 n A hA 0%N psi v)-
    zero_form_value (@current_test_value R h2 n A hA 0%N psi u)).
  by rewrite !dirac_current_evaluation.
by rewrite hDifference.
Qed.
End OrientedSegmentCurrentBoundary.
