(** Federer (1969), 3.2.48, p. 284: applying the
    original-domain coarea fibre theorem to Psi. The actual
    compact orthogonal group supplies the target premises, and
    the printed original A,B hypotheses supply the source. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric EuclideanHomInnerCharts OrthogonalMaps
  EuclideanOrthogonalAdjointInverse EuclideanRectangularAdjoint
  EuclideanStiefelCompact EuclideanStiefelSmooth FiniteInnerSmoothSubmanifoldUP
  FiniteInnerCompactSubmanifold FiniteInnerCartesianChart FiniteInnerCoareaFibres
  UnitSphereSpace SphericalProductPreimageImage SphericalKinematicSource
  OrthogonalKinematicMap OrthogonalKinematicLipschitz OrthogonalKinematicDimensions
  ProductInner LipschitzUP LipschitzBasic RectifiableSetUP HausdorffMeasure
  HausdorffClosedCoverAgreement BorelRegularMeasureUP TopologicalBorel MeasureUP
  MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_group_measure_rectifiable]: the actual
    compact target O(N) of the coarea application in
    3.2.48, p. 284, is finitely H^nu rectifiable
    and measurable. These are consequences of 3.2.28(1),
    p. 263, including N=0, rather than extra premises. *)
Lemma orthogonal_group_measure_rectifiable (R:realType) N:
  let H:=inner_metric_space (@euclidean_hom_inner_productP R N N) in
  let O:=[set g:Hom (R_n R N) (R_n R N)|is_orthogonal_map
    (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear g)] in
  is_measure_m_rectifiable (@hausdorff_measure R H (N*(N-1)%/2)) (N*(N-1)%/2)%N O /\
  measure_measurable (@hausdorff_measure R H (N*(N-1)%/2)) O.
Proof.
move=>H O.
have hCompact:@compact H O:=@euclidean_stiefel_compact R N N.
have hRect:=@finite_inner_compact_submanifold_measure_rectifiable R
  (Hom (R_n R N) (R_n R N)) _ (@euclidean_hom_inner_productP R N N)
  (N*(2*N-N-1)%/2)%N 1 O O (leqnn 1)
  (inner_smooth_submanifold_class (@euclidean_stiefel_smooth_submanifold R N N) 1%N)
  (@subset_refl (Hom (R_n R N) (R_n R N)) O) hCompact.
rewrite mul2n -addnn addKn in hRect.
split; first exact hRect.
apply:(borel_regular_borel_measurable (@hausdorff_measure_is_measure R H (N*(N-1)%/2)%N)
  (@hausdorff_measure_borel_regular R H (N*(N-1)%/2)%N)).
exact (closed_borel_set (compact_closed (@metric_hausdorff R H) hCompact)).
Qed.

(** Source for [orthogonal_kinematic_coarea_fibres]: the actual
    whole Psi fibre is finitely H^(lambda+mu) rectifiable
    and completed measurable for H^nu almost every g
    in O(d+1), 3.2.48, p. 284. No derivative,
    transversality, finite-fibre or Borel-source assumption is added.
    The ambient polynomial is only required to be Lipschitz
    on its actual compact orthogonal domain, which is proved. *)
Theorem orthogonal_kinematic_coarea_fibres (R:realType) d k m (c:R_n R d.+1)
    (A B:set (R_n R d.+1)):
  (d<=k+m)%N ->inner_norm (@euclidean_inner_productP R d.+1) c= 1 ->
  A `<=` @euclidean_unit_sphere_set R d.+1 ->B `<=` @euclidean_unit_sphere_set R d.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) k) k A ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) k) A ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R d.+1)) m B ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) m) B ->
  let H:=inner_metric_space (@euclidean_hom_inner_productP R d.+1 d.+1) in
  let P:=inner_metric_space (product_inner_productP
    (@euclidean_hom_inner_productP R d.+1 d.+1) (@euclidean_hom_inner_productP R d.+1 d.+1)) in
  let source:=[set z:Hom (R_n R d.+1) (R_n R d.+1)*Hom (R_n R d.+1) (R_n R d.+1)|
    spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2] in
  measure_almost_everywhere_on (@hausdorff_measure R H (d.+1*(d.+1-1)%/2))
    [set g|is_orthogonal_map (@euclidean_inner_product R d.+1)
      (@euclidean_inner_product R d.+1) (hom_as_linear g)]
    [set g|is_measure_m_rectifiable (@hausdorff_measure R P ((k+m-d)+d*(d-1)%/2))
      ((k+m-d)+d*(d-1)%/2)%N [set z|source z /\orthogonal_kinematic_map z=g] /\
      measure_measurable (@hausdorff_measure R P ((k+m-d)+d*(d-1)%/2))
        [set z|source z /\orthogonal_kinematic_map z=g]].
Proof.
move=>hDim hc hA hB hRA hMA hRB hMB H P source.
pose V:=Hom (R_n R d.+1) (R_n R d.+1).
pose Q:lmodType R:=[the lmodType R of (V*V)%type].
pose hH:=@euclidean_hom_inner_productP R d.+1 d.+1.
pose hP:=product_inner_productP hH hH.
pose O:=[set g:V|is_orthogonal_map (@euclidean_inner_product R d.+1)
  (@euclidean_inner_product R d.+1) (hom_as_linear g)].
have hSource:=@spherical_kinematic_source R d k m c A B hc hA hB hRA hMA hRB hMB.
have hTarget:=@orthogonal_group_measure_rectifiable R d.+1.
have [e [p hChart]]:=@euclidean_hom_inner_chart_exists R d.+1 d.+1.
have hProductChart:=finite_inner_cartesian_chart hH hH hChart hChart.
have hLip:@is_metric_lipschitz R P H source (@orthogonal_kinematic_map R d.+1).
  have [L [hPositive hBound]]:=@orthogonal_kinematic_lipschitz R d.+1.
  exists L; split; first exact hPositive.
  apply:(metric_lipschitz_bound_restrict _ hBound).
  move=>z [hx hy]; exact (conj hx.1 hy.1).
have hRange x:source x ->O (orthogonal_kinematic_map x).
  move=>[hx hy] u v.
  change (euclidean_inner_product (x.1 (euclidean_rectangular_adjoint x.2 u))
    (x.1 (euclidean_rectangular_adjoint x.2 v))=euclidean_inner_product u v).
  by rewrite hx.1 (euclidean_orthogonal_adjoint_orthogonal hy.1).
have hResult:=@finite_inner_coarea_fibres R Q V _ _ hP hH _ _
  ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N (d.+1*(d.+1-1)%/2)%N
  (finite_inner_cartesian_direct e e) (finite_inner_cartesian_inverse p p) e p
  source O (@orthogonal_kinematic_map R d.+1) hProductChart hChart
  (orthogonal_kinematic_target_dimension_bound hDim) hSource.1 hSource.2
  hTarget.1 hTarget.2 hLip hRange.
by rewrite (orthogonal_kinematic_fibre_dimension hDim) in hResult.
Qed.
