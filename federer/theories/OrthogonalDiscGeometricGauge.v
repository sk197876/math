(** Federer (1969), 3.2.26(2), p. 261: the
    normalized integral-geometric cost of a unit m-disc
    is alpha(m). Expand the printed normalization step
    using the actual projection constants of 2.7.16(6),
    p. 140, and linear volume scaling. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps CoordinateProjection InnerNorm InnerMetric InnerNormedTopology InnerExterior InnerExteriorPositivity
  ExteriorGrading ExteriorNorm ExteriorMaps ExteriorMapScaling ExteriorOperatorEstimate FiniteExteriorPowers
  ExteriorDiameterUP AssociatedSubspace SimpleElementary OrthogonalMaps OrthonormalFamilies EuclideanProjectionSpace
  EuclideanProjectionMetric OrthogonalProjectionConstants EuclideanLinearJacobian EuclideanTopExteriorVolume
  ExteriorDeterminant EuclideanLebesgueDimensions EuclideanLebesgueDeterminant EuclideanLebesgueBoxes
  EuclideanBallVolume EuclideanClosedBallVolume EuclideanClosedBallGrowth EuclideanAdditiveGroup MetricClosedBalls NormMetricScaleContinuity
  ProjectedVolumeMeasurability OrthogonalProjectionProbability ProjectionBeta ProjectionBetaContinuity
  IntegralGeometricGauge ExtendedRealOrderTopology SimpleProjectionExponentNorm NonnegativeExtendedNormScale
  NonnegativeExtendedExponentNorm BorelClosedProjection TopologicalBorel MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [orthogonal_unit_disc_compact]: supporting
    compactness of B(0,1) intersect Y in 3.2.26(2),
    p. 261. An orthogonal injection identifies it with
    the continuous image of the compact source unit ball. *)
Lemma orthogonal_unit_disc_compact (R:realType) m n (f:{linear R_n R m->R_n R n}):
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) f ->
  @compact (inner_metric_space (@euclidean_inner_productP R n))
    (f @` (@metric_closed_ball R (inner_metric_space (@euclidean_inner_productP R m)) (0%R:R_n R m) 1%R)).
Proof.
move=>hF.
have hContinuous:continuous (f:inner_metric_space (@euclidean_inner_productP R m)->
    inner_metric_space (@euclidean_inner_productP R n)).
  apply:(@metric_fixed_lipschitz_continuous R _ _ _ 1 ler01)=>x y.
  rewrite !inner_metric_distanceE -linearB
    (orthogonal_map_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) hF) mul1r.
  exact:lexx.
have hCompact:@compact (inner_metric_space (@euclidean_inner_productP R m))
    (@metric_closed_ball R (inner_metric_space (@euclidean_inner_productP R m)) (0%R:R_n R m) 1%R).
  rewrite euclidean_metric_closed_ballE; exact:(@euclidean_closed_ball_compact R m 0%R 1%R).
exact:(continuous_compact (continuous_subspaceT hContinuous) hCompact).
Qed.

(** Source for [linear_unit_disc_projected_volume]: the
    projected-disc volume used in 3.2.26(2), p. 261.
    A square linear image scales Lebesgue volume by the
    absolute determinant, including singular images and degree
    zero. The top exterior word evaluates that determinant. *)
Lemma linear_unit_disc_projected_volume (R:realType) m n
    (f:{linear R_n R m->R_n R n}) (p:orthogonal_projection_metric_space R n m):
  projected_volume_function
    (f @` (@metric_closed_ball R (inner_metric_space (@euclidean_inner_productP R m)) (0%R:R_n R m) 1%R)) p=
    (euclidean_unit_ball_volume R m*
      projection_norm (euclidean_two_nonzero R)
        (e_lambda (fun i=>f (@coordinate_basis R m i)) (ord_tuple m)) p)%R%:E.
Proof.
pose B:=@metric_closed_ball R (inner_metric_space (@euclidean_inner_productP R m)) (0%R:R_n R m) 1%R.
pose L:=linear_comp (euclidean_projection_linear p) f.
pose H:=hom_of_linear L.
pose omega:=e_lambda (@coordinate_basis R m) (ord_tuple m).
have hImage:euclidean_projection_linear p @` (f @` B)=L @` B.
  apply/seteqP; split=>y.
  - move=>[z [x hx <-] <-]; by exists x.
  - move=>[x hx <-]; exists (f x); first by exists x.
    reflexivity.
have hUnit:exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) omega= 1%R.
  apply:orthonormal_product_unit_norm.
  by move=>i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
have hScale:=@euclidean_top_exterior_volume_scale R m m H omega.
rewrite hUnit mulr1 in hScale.
have hWord:exterior_power_map (hom_as_linear H) m omega=
    exterior_power_map (euclidean_projection_linear p) m
      (e_lambda (fun i=>f (@coordinate_basis R m i)) (ord_tuple m)).
  rewrite /omega !exterior_map_indexed_product.
  congr (e_lambda _ _); apply:funext=>i; reflexivity.
have hJac:euclidean_linear_jacobian m H=projection_norm (euclidean_two_nonzero R)
    (e_lambda (fun i=>f (@coordinate_basis R m i)) (ord_tuple m)) p.
  rewrite -hScale hWord; reflexivity.
have hDet:euclidean_det (hom_as_linear H)=euclidean_det L.
  apply:det_ext=>x; reflexivity.
have hJacDet:=euclidean_linear_jacobian_determinant H.
rewrite hDet hJac in hJacDet.
rewrite /projected_volume_function hImage (@euclidean_lebesgue_linear_image R m L B).
rewrite (@euclidean_closed_ball_normalized_volume R m (0%R:R_n R m) 1%R ler01) expr1n mulr1.
by rewrite -EFinM -hJacDet mulrC.
Qed.

(** Source for [orthogonal_unit_disc_integral_geometric_gauge]:
    zeta_t(B(0,1) intersect Y)=alpha(m) in
    3.2.26(2), p. 261. The erratum p. 5,
    book p. 261 line 22, identifies zeta_t with
    2.10.5. Its actual beta_t normalization cancels
    the simple unit projection norm for every t>=1. *)
Theorem orthogonal_unit_disc_integral_geometric_gauge (R:realType) m n
    (hmn:(m<=n)%N) (f:{linear R_n R m->R_n R n}) (t: \bar R):
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) f ->1<=t ->
  @integral_geometric_gauge R n m hmn t
    (f @` (@metric_closed_ball R (inner_metric_space (@euclidean_inner_productP R m)) (0%R:R_n R m) 1%R))=
    (euclidean_unit_ball_volume R m)%:E.
Proof.
move=>hF ht.
pose P:=orthogonal_projection_metric_space R n m.
pose theta:=@orthogonal_projection_probability R n m hmn.
pose A:=f @` (@metric_closed_ball R (inner_metric_space (@euclidean_inner_productP R m)) (0%R:R_n R m) 1%R).
pose xi:=e_lambda (fun i=>f (@coordinate_basis R m i)) (ord_tuple m).
pose alpha:=euclidean_unit_ball_volume R m.
pose g (p:P):extended_real_line R:=(projection_norm (euclidean_two_nonzero R) xi p)%:E.
have hAlpha:(0<alpha)%R:=(euclidean_unit_ball_volumeE R m).2.
have hSimple:simple xi:=product_simple _.
have hUnit:exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) xi= 1%R.
  apply:orthonormal_product_unit_norm.
  move=>i j; rewrite hF euclidean_inner_basis /coordinate_basis ffunE eq_sym; reflexivity.
have hFormula p:projected_volume_function A p=alpha%:E*g p.
  rewrite /A linear_unit_disc_projected_volume -EFinM; reflexivity.
have hMeasA:=@theta_star_projected_volume_measurable R n m hmn A
  (metric_borel_suslin (closed_borel_set (compact_closed
    (@metric_hausdorff R (inner_metric_space (@euclidean_inner_productP R n)))
      (orthogonal_unit_disc_compact hF)))).
have hMeas:=@measurable_total_extended_scale R P theta (@theta_star_is_measure R n m hmn)
  (projected_volume_function A) (alpha^-1)%R hMeasA.
have hAlphaNonzero:alpha!=0%R by rewrite gt_eqF.
have hCancel:(fun p:P=>(alpha^-1)%R%:E*projected_volume_function A p)=g.
  apply:funext=>p; rewrite hFormula muleA -EFinM (mulVf hAlphaNonzero) ?mul1e ?mul1r; reflexivity.
rewrite hCancel in hMeas.
have hFunction:projected_volume_function A=(fun p:P=>alpha%:E*g p).
  apply:funext; exact hFormula.
rewrite /integral_geometric_gauge hFunction
  (@nonnegative_extended_norm_scale R P theta (@theta_star_is_measure R n m hmn) g t alpha
    (fun p=>projection_norm_nonnegative (euclidean_two_nonzero R) xi p) ht (ltW hAlpha) hMeas).
have hNorm:=@simple_projection_extended_exponent_norm R n m hmn xi t hSimple ht.
rewrite (Prop_irrelevance (real_exterior_two_nonzero R) (euclidean_two_nonzero R)) in hNorm.
rewrite hUnit mulr1 in hNorm.
change (is_true (0<alpha)%R) in hAlpha.
rewrite hNorm muleA -!EFinM.
congr (_%:E).
rewrite mulrAC mulVf ?mul1r //; by rewrite gt_eqF //; exact:projection_beta_positive ht.
Qed.
