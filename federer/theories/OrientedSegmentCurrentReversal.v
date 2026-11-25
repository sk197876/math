(** Federer (1969), 4.1.8, p. 362: reversal
    negates the original segment current. Reuse the
    original scalar reflection integral and finite
    homogeneity, preserving all actual tests. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology normedtype.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorPowers AlternatingPairing
  CurrentCoefficientNorms CurrentSpaces CurrentEvaluation CurrentPointEvaluation
  CurrentSegmentMapUP CurrentSegmentReflection OrientedSegmentCurrentUP OrientedSegmentCurrentSealed
  ConvexMetricSegment RealMetricBackground ExtendedRealOrderTopology LebesgueScalarMeasure
  ScalarIntervalIsometryIntegral RealSubsetFiniteScale PartialFunctionUP PartialFunctionPrecomposition
  PartialZeroExtension MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  MeasureIntegralUniqueness SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OrientedSegmentCurrentReversal.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Variable A:set X.
Hypothesis hA:forall x,A x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) A x.
Variables u v:X.
Hypothesis hSegment:@is_current_segment_domain R n A u v.
Hypothesis hReverse:@is_current_segment_domain R n A v u.
Local Notation S := (@OrientedSegmentCurrent.value R h2 n A hA u v hSegment).
Local Notation T := (@OrientedSegmentCurrent.value R h2 n A hA v u hReverse).
Local Notation value := (@current_test_value R h2 n A hA 1%N).
Local Notation Leb := (@lebesgue_scalar_measure R).
Local Notation I := (`[0,1]:set (real_line_metric R)).

(** Source for [oriented_segment_current_reversal]:
    [v,u]=-[u,v], the original orientation reversal
    in Federer 4.1.8, p. 362. Both zero
    velocity and zero-dimensional ambient spaces remain. *)
Theorem oriented_segment_current_reversal:T= -S.
Proof.
apply:(@current_values_extensional R h2 n 1%N A hA)=>phi.
pose f t:=pairing (exterior_first_inclusion X (v-u)) (value phi (metric_segment_point u v t)).
pose g t:=pairing (exterior_first_inclusion X (u-v)) (value phi (metric_segment_point v u t)).
have hAction:=@OrientedSegmentCurrent.laws R h2 n A hA u v hSegment phi.
have hReflect:=@scalar_interval_reflection_integral R (real_total_integrand f) 0 1
  (@current_value R h2 n A hA 1%N S phi)%:E hAction.
have hActual:is_measure_subset_integral Leb I (real_total_integrand (fun t=>f (1-t)))
    (@current_value R h2 n A hA 1%N S phi)%:E.
  apply:(measure_integral_graph_equivalent _ hReflect)=>t z.
  have hInner:partial_function_graph (partial_function_precompose (fun t:R=>0+1-t)
      (real_total_integrand f)) t z <->
      partial_function_graph (real_total_integrand (fun t=>f (1-t))) t z.
    change (partial_function_graph (real_total_integrand f) (0+1-t) z <->
      partial_function_graph (real_total_integrand (fun t=>f (1-t))) t z).
    by rewrite !real_total_integrand_graph add0r.
  by rewrite !partial_function_zero_extension_graph hInner.
have hVelocity:u-v=(-1:R)*:(v-u) by rewrite scaleN1r opprB.
have hScale t:I t->g t=(-1:R)*f (1-t).
  move=>_;rewrite /g /f current_segment_parameter_reflection hVelocity linearZ.
  exact:(bilZl (@pairing_bilinear R X R^o 1%N) (-1:R)
    (exterior_first_inclusion X (v-u)) (value phi (metric_segment_point v u t))).
have hNegative:=@real_subset_integral_multiply_finite_scale R (real_line_metric R) Leb
  (lebesgue_scalar_is_measure R) I g (fun t=>f (1-t))
  (@current_value R h2 n A hA 1%N S phi) (-1) (ltac:(by rewrite oppr_eq0 oner_eq0)) hScale hActual.
rewrite mulN1r in hNegative.
have hReverseAction:=@OrientedSegmentCurrent.laws R h2 n A hA v u hReverse phi.
have hValue:=EFin_inj (measure_integral_unique hReverseAction hNegative).
by rewrite current_value_negate.
Qed.
End OrientedSegmentCurrentReversal.
