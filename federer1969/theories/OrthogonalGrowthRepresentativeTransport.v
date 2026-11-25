(** Federer (1969), 3.4.8(13), pp. 328, 336:
    return the compact growth representative to the original
    coordinates. Exact germ transport, finite rectifiability and
    the uniform growth coefficient all use existing public laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric InnerNorm HilbertFormCompactness NormFiniteLinearBound NormBoundedLinearTopology GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  OrthogonalMaps OrthogonalFinite OrthogonalHausdorffImage MetricIsometricImageGeometry
  SetGermUP SetGermCoordinateImage RectifiableSetUP FiniteMeasureRectifiableImages LipschitzUP
  HausdorffMeasure UniformHausdorffGrowthUP UniformHausdorffGrowthOrthogonalImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_growth_representative_transport]: the
    representative S of the original alpha in
    3.4.8(13), pp. 328, 336. Orthogonal
    transport preserves its actual germ and every growth bound. *)
Theorem orthogonal_growth_representative_transport (R:realType) n m
    (f:{linear R_n R n->R_n R n}) (S H:set (R_n R n)) (c:R):
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) f ->
  @compact (inner_metric_space (@euclidean_inner_productP R n)) S ->
  @set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 S=
    @set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 (f @^-1` H) ->
  @is_measure_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n))
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) m S ->
  @is_uniform_hausdorff_growth R (inner_metric_space (@euclidean_inner_productP R n)) m S c ->
  @compact (inner_metric_space (@euclidean_inner_productP R n)) (f @` S) /\
  @set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 (f @` S)=
    @set_germ (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 H /\
  @is_measure_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n))
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) m (f @` S) /\
  @is_uniform_hausdorff_growth R (inner_metric_space (@euclidean_inner_productP R n)) m (f @` S) c.
Proof.
move=>hF hCompact hGerm hRect hGrowth.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose Top:=Topological.clone (real_norm_metric_space hNX) _.
have [g [hFG [hGF hG]]]:=@orthogonal_endomorphism_inverse_exists R (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) n
  (@coordinate_basis R n) (@coordinate_basisP R n) f hF.
have hDistance (u:{linear R_n R n->R_n R n})
    (hU:is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) u)
    (x y:X):@mdist R X (u x) (u y)=mdist x y.
  by rewrite !inner_metric_distanceE -linearB
    (orthogonal_map_norm (@euclidean_inner_productP R n) (@euclidean_inner_productP R n) hU).
have hFContinuous:=@metric_isometric_map_continuous R X X f (hDistance f hF).
have hGContinuous:=@metric_isometric_map_continuous R X X g (hDistance g hG).
have hGBound:=@norm_finite_linear_bounded R (R_n R n) (R_n R n) NX NX hNX hNX
  n (@coordinate_basis R n) (@coordinate_basisP R n) (hom_of_linear g).
have hGNorm:=@norm_bounded_linear_continuous R (R_n R n) (R_n R n) NX NX hNX hNX (hom_of_linear g) hGBound.
split;first exact:continuous_compact (continuous_subspaceT hFContinuous) hCompact.
split.
- have h:=@set_germ_coordinate_image Top 0 f g id f S H hGNorm (linear0 g) hFG hGF
    (fun x=>erefl (f x)) hGerm.
  by rewrite preimage_id in h.
split;last exact:uniform_hausdorff_growth_orthogonal_image hF hGrowth.
apply:(hausdorff_measure_rectifiable_lipschitz_image _ hRect).
exists 1;split;first exact:ltr01.
split;first exact:ler01.
move=>x y hx hy;rewrite hDistance // mul1r.
exact:lexx.
Qed.
