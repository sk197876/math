(** Federer (1969), 3.2.26(3), p. 262: take
    the parameter-space L^t norm of the lower projection
    bound on one Borel orientation piece. All exponents
    at least one, including infinity, are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps InnerMetric
  ExteriorDiameterUP ExteriorGrading ExteriorNorm AssociatedSubspace
  EuclideanProjectionMetric OrthogonalProjectionConstants OrthogonalProjectionProbability
  ProjectionBeta ProjectionBetaContinuity SimpleProjectionExponentNorm
  RectifiableSetUP RectifiableOrientationUP RectifiableProjectionMultiplicityLower
  BorelProjectionMultiplicityNorm ProbabilityNormUniformError IntegralGeometricMeasure ProjectionMultiplicityIntegral
  NonnegativeExtendedExponentNorm NonnegativeExtendedNormScale
  PartialFunctionUP PartialFunctionBasic MeasurableFunctionUP MeasurableTotalBasic
  RealNormUP NormMetric ScalarNormExtendedEmbedding BorelFunctionBasic
  ExtendedRealOrderTopology HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_orientation_piece_norm_lower]: the
    last norm inequality in 3.2.26(3), p. 262.
    Unit simplicity identifies the fixed projection norm
    with beta_t; probability controls the uniform error.
    Finite piece mass is derived from the original source,
    and the multiplicity is the actual fibre integral. *)
Theorem rectifiable_orientation_piece_norm_lower (R:realType) m n
    (hmn:(m<=n)%N) (W S:set (R_n R n))
    (T:partial_function (R_n R n) (exterior_power (R_n R n) m))
    (xi:exterior_power (R_n R n) m) (d:R) (t: \bar R):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) W ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) S ->S `<=` W ->
  is_rectifiable_measurable_orientation W T ->simple xi ->
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) xi= 1%R ->
  (0<=d)%R ->1<=t ->
  (forall w eta,S w ->partial_function_graph T w eta ->
    (exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) (eta-xi)<=d)%R) ->
  (@projection_beta R n m hmn t)%:E*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m S<=
  (@projection_beta R n m hmn t)%:E*@integral_geometric_measure R n m hmn t S+d%:E*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m S.
Proof.
move=>hRect hW hS hSW hT hSimple hUnit hd ht hError.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
pose P:=orthogonal_projection_metric_space R n m.
pose theta:=@orthogonal_projection_probability R n m hmn.
pose g (p:P):extended_real_line R:=(projection_norm (euclidean_two_nonzero R) xi p)%:E.
have hTheta:=@theta_star_is_measure R n m hmn.
have hH:=@hausdorff_measure_is_measure R X m.
have hFinite:H S < +oo:=le_lt_trans (measure_mono hH hSW) hRect.2.
have hFin:H S \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hH S)).
pose b:R:=fine (H S).
have hMass:H S=b%:E by rewrite /b fineK.
have hb:(0<=b)%R.
  have h:=measure_nonnegative hH S.
  change (is_true (0<=H S)) in h; by rewrite hMass lee_fin in h.
have hScalar:=@simple_projection_norm_scalar_measurable R n m hmn xi hSimple.
rewrite (Prop_irrelevance (real_exterior_two_nonzero R) (euclidean_two_nonzero R)) in hScalar.
have hG:is_measure_measurable_function theta (partial_function_total g).
  apply:(@measurable_total_borel_postcomposition R P
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    (extended_real_line R) theta hTheta _ (fun y=>y%:E) hScalar).
  apply:continuous_borel_function; exact:scalar_norm_extended_embedding_continuous.
have hG0 p:0<=g p.
  rewrite /g lee_fin; exact:projection_norm_nonnegative.
have [hMult hNormMult]:=@borel_projection_multiplicity_norm R n m hmn S t hS ht.
have hErrorPoint p:b%:E*g p<=projection_multiplicity_integral S p+(d*b)%R%:E.
  have h:=@rectifiable_projection_multiplicity_uniform_lower R m n W S T xi d p
    hRect hW hS hSW hT hd hError.
  change (is_true (g p*H S<=projection_multiplicity_integral S p+d%:E*H S)) in h.
  by rewrite hMass muleC -EFinM in h.
have hNorm:=@probability_extended_norm_uniform_error R P theta t
  (fun p=>b%:E*g p) (projection_multiplicity_integral (m:=m) S) (d*b)%R
  hTheta (@theta_star_total R n m hmn) ht (mulr_ge0 hd hb)
  (fun p=>mule_ge0 (lee_tofin hb) (hG0 p))
  (fun p=>projection_multiplicity_integral_nonnegative p hS)
  (@measurable_total_extended_scale R P theta hTheta g b hG) hMult hErrorPoint.
rewrite (@nonnegative_extended_norm_scale R P theta hTheta g t b
  hG0 ht hb hG) in hNorm.
have hSimpleNorm:=@simple_projection_extended_exponent_norm R n m hmn xi t hSimple ht.
rewrite (Prop_irrelevance (real_exterior_two_nonzero R) (euclidean_two_nonzero R)) hUnit mulr1 in hSimpleNorm.
rewrite hSimpleNorm in hNorm.
have hFinal:=le_trans hNorm (leeD2r ((d*b)%R%:E) hNormMult).
change (is_true ((@projection_beta R n m hmn t)%:E*H S<=
  (@projection_beta R n m hmn t)%:E*@integral_geometric_measure R n m hmn t S+d%:E*H S)).
rewrite hMass [(@projection_beta R n m hmn t)%:E*b%:E]muleC -EFinM.
exact hFinal.
Qed.
