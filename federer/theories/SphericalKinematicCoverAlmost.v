(** Federer (1969), 3.2.48, p. 285: the null remainders
    of the two manifold covers give a null remainder in the actual
    source product. The genuine second-factor hypothesis supplies the
    exact Cartesian measure; arbitrary completed measurable sets remain. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts ProductInner UnitSphereSpace SphericalProductPreimageImage SphericalOrthogonalPullback
  SphericalMeasurablePullback SphericalOrthogonalPullback RectifiableSetUP RectifiableFiniteHausdorffMass
  HausdorffMeasure MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic MeasureBasic
  ProductMeasure EuclideanCartesianAlmost FiniteInnerCompletedCartesianMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_pullback_almost]: null-remainder transport
    by 3.2.47(2), p. 283, in the source reduction of 3.2.48,
    p. 285. The truth set need not be measurable or Borel;
    its original exceptional subset is actually null. *)
Lemma spherical_pullback_almost (R:realType) d r (c:R_n R (1+d))
    (A U:set (R_n R (1+d))):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  A `<=` @euclidean_unit_sphere_set R (1+d) ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (1+d))) r (A `\` U)=0)%E ->
  measure_almost_everywhere (measure_restrict (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R (1+d) (1+d))) (r+d*(d-1)%/2))
    (spherical_orthogonal_preimage c A)) [set g:Hom (R_n R (1+d)) (R_n R (1+d))|U (g c)].
Proof.
move=>hc hA hNull.
have hPre:=@federer_3_2_47_2 R d c (A `\` U) r hc (fun x hx=>hA x hx.1) hNull.
change (@hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R (1+d) (1+d)))
  (r+d*(d-1)%/2) (spherical_orthogonal_preimage c A `&` (~` [set g|U (g c)]))=0)%E.
apply:(measure_null_subset (@hausdorff_measure_is_measure R
  (inner_metric_space (@euclidean_hom_inner_productP R (1+d) (1+d))) (r+d*(d-1)%/2)) _ hPre).
by move=>g [[hg ha] hNot]; split; last split.
Qed.

(** Source for [spherical_kinematic_cover_almost]: the actual source
    is covered almost everywhere by the products of the pulled-back
    original manifold pieces in 3.2.48, p. 285. No measurability of
    the covering families is needed for this null-remainder conclusion. *)
Theorem spherical_kinematic_cover_almost (R:realType) d k m (c:R_n R (1+d))
    (A B:set (R_n R (1+d))) (C D:set (set (R_n R (1+d)))):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  A `<=` @euclidean_unit_sphere_set R (1+d) ->B `<=` @euclidean_unit_sphere_set R (1+d) ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) k A ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) A ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R (1+d))) m B ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) m) B ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (1+d))) k
    (A `\` \bigcup_(E in C) E)=0)%E ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (1+d))) m
    (B `\` \bigcup_(E in D) E)=0)%E ->
  let P:=inner_metric_space (product_inner_productP
    (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))) in
  let S:=[set z:Hom (R_n R (1+d)) (R_n R (1+d))*Hom (R_n R (1+d)) (R_n R (1+d))|
    spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2] in
  (@hausdorff_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))
    (S `\` \bigcup_(i in C `*` D)
      [set z:Hom (R_n R (1+d)) (R_n R (1+d))*Hom (R_n R (1+d)) (R_n R (1+d))|
        spherical_orthogonal_preimage c (A `&` i.1) z.1 /\
        spherical_orthogonal_preimage c (B `&` i.2) z.2])=0)%E.
Proof.
move=>hc hA hB hRA hMA hRB hMB hLossA hLossB P S.
pose X:=inner_metric_space (@euclidean_hom_inner_productP R (1+d) (1+d)).
pose HX:=@hausdorff_measure R X (k+d*(d-1)%/2).
pose HY:=@hausdorff_measure R X (m+d*(d-1)%/2).
pose HP:=@hausdorff_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2)).
pose PA:=[set g:X|(\bigcup_(E in C) E) (g c)].
pose PB:=[set g:X|(\bigcup_(E in D) E) (g c)].
pose hAlpha:=measure_restrict_is_measure (@hausdorff_measure_is_measure R X (k+d*(d-1)%/2))
  (spherical_orthogonal_preimage c A).
pose hBeta:=measure_restrict_is_measure (@hausdorff_measure_is_measure R X (m+d*(d-1)%/2))
  (spherical_orthogonal_preimage c B).
have hAlmostA:=@spherical_pullback_almost R d k c A (\bigcup_(E in C) E) hc hA hLossA.
have hAlmostB:=@spherical_pullback_almost R d m c B (\bigcup_(E in D) E) hc hB hLossB.
have hProduct:=product_measure_almost_everywhere_factors hAlpha hBeta hAlmostA hAlmostB.
have hPullA:=@spherical_measurable_measure_rectifiable_pullback R d k c A hc hA hRA hMA.
have hPullB:=@spherical_measurable_measure_rectifiable_pullback R d m c B hc hB
  (rectifiable_hausdorff_measure_rectifiable hRB) hMB.
have hGenuine:=@federer_3_2_47_1 R d c B m hc hB hRB.
have [e [p hChart]]:=@euclidean_hom_inner_chart_exists R (1+d)%N (1+d)%N.
have hMeasure:=@finite_inner_completed_cartesian_measure_right R
  (Hom (R_n R (1+d)) (R_n R (1+d))) (Hom (R_n R (1+d)) (R_n R (1+d))) _ _
  (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))
  _ _ e p e p (k+d*(d-1)%/2)%N (m+d*(d-1)%/2)%N
  (spherical_orthogonal_preimage c A) (spherical_orthogonal_preimage c B)
  hChart hChart hPullA.1 hPullA.2 hGenuine hPullB.2.
change (product_measure hAlpha hBeta (~` (PA `*` PB))=0)%E in hProduct.
have hAt:=congr1 (fun nu:set (X*X)->\bar R=>nu (~` (PA `*` PB))) hMeasure.
have hZero:measure_restrict HP S (~` (PA `*` PB))=0%E.
  exact (eq_trans hAt hProduct).
change (HP (S `&` (~` (PA `*` PB)))=0)%E in hZero.
apply:(measure_null_subset (@hausdorff_measure_is_measure R P
  ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))) _ hZero).
move=>z [hz hNot]; split; first exact hz.
move=>[[E hE hx] [F hF hy]]; apply hNot; exists (E,F); first by split.
split.
- split; first exact hz.1.1; by split; [exact hz.1.2|exact hx].
- split; first exact hz.2.1; by split; [exact hz.2.2|exact hy].
Qed.
