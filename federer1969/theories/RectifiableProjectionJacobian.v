(** Federer (1969), 3.2.26(3), p. 262: identify
    ap J_m p with the norm of the projection of the
    simple unit tangent vector. The working erratum p. 5,
    book p. 262 line 14, invokes 3.2.20 here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ModuleQuotient Hom GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  InnerNorm InnerMetric HilbertFormCompactness InnerExterior InnerExteriorPositivity
  ExteriorGrading ExteriorNorm AssociatedSubspace EuclideanProjectionSpace EuclideanProjectionMetric
  OrthogonalProjectionConstants NormDifferentialUP RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  MeasureApproximateTangentUP MeasureApproximateDifferentialUP MeasureApproximateDifferentialUniqueness
  MeasureApproximateJacobianUP MeasureApproximateJacobian LinearMeasureApproximation
  SimpleUnitPartialExteriorNorm RectifiableOrientationUP HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [projection_jacobian_on_oriented_tangent]: the
    pointwise identity in the first displayed integral of
    3.2.26(3), p. 262. A projection is an
    actual approximate representative for the restricted measure.
    Uniqueness restricts every representative to the same tangent
    plane. The intrinsic exterior norm is evaluated on the
    actual simple unit vector, including degree zero. *)
Theorem projection_jacobian_on_oriented_tangent (R:realType) m n
    (phi:set (R_n R n)->\bar R) (W:set (R_n R n)) a
    (xi:exterior_power (R_n R n) m) (p:orthogonal_projection_metric_space R n m):
  is_measure phi ->simple xi ->
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) xi= 1 ->
  measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n))
    (measure_restrict phi W) m a=[set v|FedererSimple.T xi v] ->
  partial_function_graph (measure_approximate_jacobian (measure_restrict phi W) m m
    (partial_function_source_restrict W (partial_function_total (euclidean_projection_linear p))))
    a (projection_norm (euclidean_two_nonzero R) xi p).
Proof.
move=>hPhi hSimple hUnit hCone.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NY:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose mu:=measure_restrict phi W.
pose L:=hom_of_linear (euclidean_projection_linear p).
pose f:=partial_function_source_restrict W (partial_function_total (euclidean_projection_linear p)).
have hMu:=measure_restrict_is_measure hPhi W.
have hBound:norm_bounded_linear NX NY L.
  exists 1; split; first exact:ler01.
  move=>v.
  have h:=@euclidean_projection_nonexpanding R n m p v 0.
  rewrite linear0 !inner_metric_distanceE !subr0 in h.
  by rewrite mul1r.
have hApprox:=@restricted_linear_measure_approximation R (R_n R n) (R_n R m)
  NX NY hNX hNY phi m W a L hPhi hBound.
have hSingle v y z:(FedererSimple.T xi v /\euclidean_projection_linear p v=y) ->
    (FedererSimple.T xi v /\euclidean_projection_linear p v=z) ->y=z.
  move=>[_ hy] [_ hz]; exact:(eq_trans (esym hy) hz).
pose d:=@Build_partial_function (R_n R n) (R_n R m)
  (fun v y=>FedererSimple.T xi v /\euclidean_projection_linear p v=y) hSingle.
have hPoint v:measure_approximate_tangent_cone hNX mu m a v <->FedererSimple.T xi v.
  by rewrite hCone.
have hd:is_measure_approximate_differential NY hNX mu m f a d.
  split; first by exists L.
  move=>v y; split.
  - move=>[hv hy]; split; first exact:(hPoint v).2 hv.
    exists L; by split.
  - move=>[hv [D [hD hDy]]]; split; first exact:(hPoint v).1 hv.
    have hEqual:=@measure_approximate_linear_maps_agree_on_cone R (R_n R n) (R_n R m)
      NX NY hNX hNY mu m f a L D hMu hApprox hD v hv.
    exact:(eq_trans hEqual hDy).
apply:(measure_approximate_jacobian_graph _ _ _ _ _ _).2.
exists d; split; first exact hd.
apply:(@simple_unit_projection_partial_exterior_norm R m n xi p d hSimple hUnit).
by move=>v y.
Qed.

(** Source for [rectifiable_orientation_projection_jacobians]: the
    common almost-everywhere tangent qualifier in 3.2.26(3),
    p. 262. On one conull source set, every
    orthogonal projection has its actual approximate Jacobian
    equal to its norm on the actual orientation value. *)
Theorem rectifiable_orientation_projection_jacobians (R:realType) m n
    (W:set (R_n R n))
    (T:partial_function (R_n R n) (exterior_power (R_n R n) m)):
  is_rectifiable_measurable_orientation W T ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W [set w|
    exists xi,partial_function_graph T w xi /\
      forall p:orthogonal_projection_metric_space R n m,
        partial_function_graph (measure_approximate_jacobian (measure_restrict
          (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W) m m
          (partial_function_source_restrict W (partial_function_total (euclidean_projection_linear p))))
          w (projection_norm (euclidean_two_nonzero R) xi p)].
Proof.
move=>hT.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
have hH:=@hausdorff_measure_is_measure R X m.
apply:(measure_null_subset hH _ (rectifiable_orientation_tangent hT))=>w [hw hn].
split; first exact hw.
move=>[xi [hValue [hCone _]]]; apply:hn.
exists xi; split; first exact hValue; move=>p.
have [hSimple hUnit]:=rectifiable_orientation_unit_simple hT hValue.
exact:(@projection_jacobian_on_oriented_tangent R m n H W w xi p hH hSimple hUnit hCone).
Qed.
