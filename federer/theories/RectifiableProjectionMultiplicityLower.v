(** Federer (1969), 3.2.26(3), p. 262: integrate
    the projection norm on a Borel orientation piece.
    The actual multiplicity integral is within delta times
    the piece's Hausdorff mass of the fixed-vector profile. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps InnerMetric
  InnerExterior InnerExteriorPositivity ExteriorGrading ExteriorNorm AssociatedSubspace
  EuclideanProjectionSpace EuclideanProjectionMetric OrthogonalProjectionConstants ProjectionNormUniformError
  PartialFunctionUP PartialFunctionSourceRestriction PartialFunctionPostcomposition RectifiableSetUP RectifiableOrientationUP
  RectifiableSubsetProjectionJacobian CountablyMeasureRectifiableOperations
  ProjectionAreaJacobianIntegral ProjectionMultiplicityIntegral MeasureApproximateJacobian
  SubsetIntegralAlmostConstantLower HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  BorelRegularMeasureUP TopologicalBorel ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_projection_multiplicity_uniform_lower]: the
    first integral inequality in 3.2.26(3), p. 262,
    written with the error moved to the right. The
    statement uses the actual projection multiplicity integral
    and the original partial orientation field. A nonpositive
    constant lower bound is handled by nonnegativity; a
    positive one is integrated by the corrected 3.2.20
    reference. Finite source mass justifies the scalar identity. *)
Theorem rectifiable_projection_multiplicity_uniform_lower (R:realType) m n
    (W S:set (R_n R n)) (T:partial_function (R_n R n) (exterior_power (R_n R n) m))
    (xi:exterior_power (R_n R n) m) (d:R) (p:orthogonal_projection_metric_space R n m):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) W ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) S ->S `<=` W ->
  is_rectifiable_measurable_orientation W T ->(0<=d)%R ->
  (forall w eta,S w ->partial_function_graph T w eta ->
    (exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) (eta-xi)<=d)%R) ->
  (projection_norm (euclidean_two_nonzero R) xi p)%:E*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m S<=
  projection_multiplicity_integral S p+d%:E*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m S.
Proof.
move=>hRect hW hS hSW hT hd hError.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
have hH:=@hausdorff_measure_is_measure R X m.
have hSMeas:=borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R X m) hS.
have hSFinite:H S < +oo:=le_lt_trans (measure_mono hH hSW) hRect.2.
have hSRect:is_measure_m_rectifiable H m S.
  split; last exact hSFinite.
  exact:(@countably_measure_rectifiable_subset R X H m W S hSW hRect.1).
have hMassFinite:H S \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative hH S)).
pose b:R:=fine (H S).
have hMass:H S=b%:E by rewrite /b fineK.
have hGNonnegative:=@projection_multiplicity_integral_nonnegative R n m S p hS.
pose gamma:R:=(projection_norm (euclidean_two_nonzero R) xi p-d)%R.
have [hGamma|hGamma]:=ltP 0%R gamma.
- have hArea:=@projection_area_jacobian_integral R m n S p hSRect hS.
  pose f:=partial_function_source_restrict S (PartialFunctionBasic.partial_function_total (euclidean_projection_linear p)).
  pose J:=extended_measure_approximate_jacobian (measure_restrict H S) m m f.
  have hPoint:=@rectifiable_orientation_subset_projection_jacobians R m n W S T hW hS hSW hRect.2 hT.
  have hLower:measure_almost_everywhere_on H S [set w|exists z,partial_function_graph J w z /\gamma%:E<=z].
    apply:(measure_null_subset hH _ hPoint)=>w [hw hn]; split; first exact hw.
    move=>[eta [hValue hJacobian]]; apply:hn.
    have hEstimate:=@projection_norm_nearby_lower R m n xi eta p d (hError w eta hw hValue).
    exists (projection_norm (euclidean_two_nonzero R) eta p)%:E; split.
    + exists (projection_norm (euclidean_two_nonzero R) eta p); split; first exact:hJacobian p.
      reflexivity.
    + rewrite lee_fin; exact hEstimate.
  have hIntegral:=@subset_integral_almost_positive_constant_lower R (Choice.clone X _) H S J
    (projection_multiplicity_integral S p) gamma hH hSMeas hGamma hArea hLower.
  have hIdentity:(projection_norm (euclidean_two_nonzero R) xi p)%:E*H S=
      gamma%:E*H S+d%:E*H S.
    rewrite hMass -!EFinM -EFinD; congr (_%:E).
    rewrite /gamma; ring.
  rewrite hIdentity; exact:(leeD2r (d%:E*H S) hIntegral).
- have hCoefficient:(projection_norm (euclidean_two_nonzero R) xi p<=d)%R.
    rewrite /gamma in hGamma; lra.
  have hSmall:=lee_wpmul2r (measure_nonnegative hH S) (lee_tofin hCoefficient).
  have hAdd:=leeD2r (d%:E*H S) hGNonnegative.
  rewrite add0e in hAdd.
  exact:(le_trans hSmall hAdd).
Qed.
