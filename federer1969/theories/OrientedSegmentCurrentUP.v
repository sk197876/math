(** Federer (1969), 4.1.8, p. 362: independent
    specification of the original oriented segment current
    by its printed scalar interval integral. Existence,
    uniqueness, reversal and boundary are proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorPowers AlternatingPairing
  CurrentSpaces ConvexMetricSegment LebesgueScalarMeasure MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section OrientedSegmentCurrentUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Variable A:set X.
Hypothesis hA:forall x,A x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) A x.
Variables u v:X.
Local Notation DT := (@current_test_space R h2 n A hA 1%N).
Local Notation C := (@current_space R h2 n A hA 1%N).
Local Notation velocity := (exterior_first_inclusion X (v-u)).

(** Source for [is_oriented_segment_current]: the original
    [u,v](alpha) is the scalar Lebesgue integral from zero
    to one of <v-u,alpha((1-t)u+tv)>, Federer 4.1.8,
    p. 362. The canonical exterior one-vector identification
    expresses the printed vector pairing. *)
Definition is_oriented_segment_current (T:C):Prop:=
  forall phi:DT,is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,1]
    (real_total_integrand (fun t=>pairing velocity
      (@current_test_value R h2 n A hA 1%N phi (metric_segment_point u v t))))
    (@current_value R h2 n A hA 1%N T phi)%:E.
End OrientedSegmentCurrentUP.
