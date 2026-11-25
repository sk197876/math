(** Federer (1969), 3.2.27, p. 263: the
    projection multiplicity integral equals the integral
    of the projection norm of the 3.2.25 orientation.
    Apply the actual 3.2.20 formula to completed
    Hausdorff-measurable finite rectifiable sources. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps InnerMetric
  ExteriorGrading ExteriorNorm EuclideanProjectionSpace EuclideanProjectionMetric OrthogonalProjectionConstants
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionPostcomposition
  RectifiableSetUP RectifiableOrientationUP RectifiableProjectionJacobian
  MeasurableProjectionAreaJacobianIntegral MeasureApproximateJacobian ProjectionMultiplicityIntegral
  HausdorffMeasure MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureSubsetIntegral RestrictedIntegralIdentity MeasureIntegralAlmostEquality
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_orientation_projection_integral]: the
    equality a_lambda=integral Xi_lambda in 3.2.27,
    p. 263, before specialising to coordinate projections.
    The intrinsic Jacobian and the exact partial
    orientation graph agree on a conull source set.
    Restriction of the measure preserves the actual
    integral and its partial domain. *)
Lemma rectifiable_orientation_projection_integral (R:realType) m n
    (W:set (R_n R n))
    (T:partial_function (R_n R n) (exterior_power (R_n R n) m))
    (p:orthogonal_projection_metric_space R n m):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_rectifiable_measurable_orientation W T ->
  is_measure_integral (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W)
    (partial_function_postcompose T
      (fun xi=>(projection_norm (euclidean_two_nonzero R) xi p)%:E:extended_real_line R))
    (projection_multiplicity_integral W p).
Proof.
move=>hRect hW hT.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
pose mu:=measure_restrict H W.
have hH:=@hausdorff_measure_is_measure R X m.
have hMu:=measure_restrict_is_measure hH W.
pose f:=partial_function_source_restrict W (partial_function_total (euclidean_projection_linear p)).
pose J:=extended_measure_approximate_jacobian mu m m f.
have hArea:=@measurable_projection_area_jacobian_integral R m n W p hRect hW.
have hIntegral:is_measure_integral mu J (projection_multiplicity_integral W p).
  exact:(@restricted_integral_zero_extension_iff R (Choice.clone X _) H hH W J _ hW).2 hArea.
have hPoint:=@rectifiable_orientation_projection_jacobians R m n W T hT.
have hAE:measure_almost_everywhere mu [set w|
    exists xi,partial_function_graph T w xi /\
      forall q:orthogonal_projection_metric_space R n m,
        partial_function_graph (measure_approximate_jacobian mu m m
          (partial_function_source_restrict W (partial_function_total (euclidean_projection_linear q))))
          w (projection_norm (euclidean_two_nonzero R) xi q)].
  rewrite /measure_almost_everywhere /mu /measure_restrict -setDE.
  exact hPoint.
apply:(@measure_integral_almost_equal R (Choice.clone X _) mu hMu _ _ _ hIntegral).
apply:(measure_almost_everywhere_mono hMu _ hAE)=>w [xi [hValue hJacobian]].
exists (projection_norm (euclidean_two_nonzero R) xi p)%:E; split.
- exists (projection_norm (euclidean_two_nonzero R) xi p); split; first exact:hJacobian p.
  reflexivity.
- exists xi; by split.
Qed.
