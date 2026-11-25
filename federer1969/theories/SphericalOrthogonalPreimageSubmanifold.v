(** Federer (1969), 3.2.47, p. 283: when E is
    an r-dimensional class-one sphere submanifold, its actual
    orthogonal-group preimage is an (r+mu)-dimensional submanifold.
    The proof uses the explicit printed product charts and
    open restriction, without assuming a bundle theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies OrthogonalMaps PartialFunctionUP
  EuclideanHomInnerCharts EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  FiniteInnerChartUP FiniteInnerSubmanifoldUP FiniteInnerCoordinatesSubmanifold
  EuclideanSubmanifoldUP SubmanifoldOpenRestriction SubmanifoldStraighteningLocalAgreement
  NormDifferentialUP NormRegularity NormRegularityLinearMaps NormFiniteLinearBound
  NormClassZeroTopology NormMetric UnitSphereSpace
  SphericalOrthogonalSectionUP SphericalOrthogonalSection SphericalOrthogonalSectionValues
  SphericalOrthogonalProductChart SphericalOrthogonalOrbitDifferential SphericalBasePointBasis
  SphericalProductPreimageImage SphericalPatchPreimageCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_basis_preimage_submanifold]: actual
    preimage submanifold in 3.2.47, p. 283, for
    a local basis beginning with c. Each point uses
    the translated printed patch centred at its own image;
    no compactness of E is needed. *)
Theorem spherical_basis_preimage_submanifold (R:realType) n r k
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e)
    (hON:orthonormal_family (@euclidean_inner_product R n.+1) e)
    (E:set (R_n R n.+1)):
  (1<=k)%N ->@is_euclidean_submanifold R n.+1 r k E ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  is_inner_submanifold (@euclidean_hom_inner_product R n.+1 n.+1)
    (r+n*(n-1)%/2)%N k (spherical_orthogonal_preimage (e ord0) E).
Proof.
move=>hk hMan hSphere.
pose V:=R_n R n.+1.
pose H:=Hom V V.
pose hV:=@euclidean_inner_productP R n.+1.
pose hH:=@euclidean_hom_inner_productP R n.+1 n.+1.
pose hNV:=inner_norm_real_norm hV.
pose hNH:=inner_norm_real_norm hH.
pose S:=spherical_orthogonal_preimage (e ord0) E.
have [eH [pH hChart]]:=@euclidean_hom_inner_chart_exists R n.+1 n.+1.
pose d:=(n.+1*n.+1)%N.
pose Z:=R_n R d.
pose hNZ:=inner_norm_real_norm (@euclidean_inner_productP R d).
exists d,eH,pH; split; first exact hChart.
move=>z [g hg <-].
have [F [hSmooth _]]:=@spherical_orthogonal_product_chart_exists R n e he hON g hg.1.
pose U:=fun a:V=>spherical_frame_cone e (euclidean_rectangular_adjoint g a).
have hAdj:=@norm_finite_linear_bounded R V V _ _ hNV hNV n.+1
  (@coordinate_basis R n.+1) (@coordinate_basisP R n.+1) (euclidean_rectangular_adjoint g).
have hUClass:=@norm_class_precompose_linear R V V H _ _ _ hNV hNV hNH
  (spherical_frame_cone e) F (euclidean_rectangular_adjoint g) 0%N hAdj (hSmooth 0%N).
have hUOpen:=@norm_class_zero_domain_open R V H _ _ hNV U
  (fun a=>F (euclidean_rectangular_adjoint g a)) (norm_class_continuous hUClass).
pose E':=E `&` U.
have hEMan:=@euclidean_submanifold_open_restriction R n.+1 r k E U hMan hUOpen.
have hInnerMan:is_inner_submanifold (@euclidean_inner_product R n.+1) r k E'.
  pose idV:Hom V V:=hom_of_linear (linear_id V).
  have hId:is_finite_inner_chart (@euclidean_inner_product R n.+1) idV idV.
    by constructor.
  exists n.+1,idV,idV; split; first exact hId.
  have hImage:idV @` E'=E'.
    apply/seteqP; split=>a; first by move=>[b hb <-].
    by move=>ha; exists a.
  by rewrite hImage.
have hBasePatch:spherical_frame_patch e (e ord0).
  have hGraph:=@spherical_section_base_point R n e he hON.
  have hDomain:partial_function_domain (spherical_orthogonal_section he) (e ord0).
    by exists (hom_of_linear (linear_id V)).
  by rewrite spherical_orthogonal_section_domain in hDomain.
have hgU:U (g (e ord0)).
  change (spherical_frame_cone e (euclidean_rectangular_adjoint g (g (e ord0)))).
  rewrite (euclidean_orthogonal_adjoint_cancel hg.1); exact hBasePatch.2.
have hE'Patch a (ha:E' a):spherical_frame_patch e (euclidean_rectangular_adjoint g a).
  split; last exact ha.2.
  rewrite (orthogonal_map_norm hV hV (euclidean_orthogonal_adjoint_orthogonal hg.1)).
  exact (hSphere a ha.1).
pose S':=spherical_orthogonal_preimage (e ord0) E'.
have hgS':S' g by split; [exact hg.1|exact (conj hg.2 hgU)].
have hS'Man:@is_euclidean_submanifold R d (r+n*(n-1)%/2)%N k (pH @` S').
  apply:(@finite_inner_coordinates_euclidean_submanifold R H _ hH d eH pH
    (r+n*(n-1)%/2)%N k S' hk hChart).
  move=>a ha.
  exact (@spherical_patch_preimage_coordinates R n r k e he hON g E' a
    hg.1 hE'Patch hInnerMan ha).
pose L:Hom Z V:=hom_comp (euclidean_rectangular_adjoint g)
  (hom_comp (spherical_orthogonal_orbit (e ord0)) eH).
pose N:=fun x:Z=>spherical_frame_cone e (L x).
have hL:=@norm_finite_linear_bounded R Z V _ _ hNZ hNV d
  (@coordinate_basis R d) (@coordinate_basisP R d) L.
have hNClass:=@norm_class_precompose_linear R Z V H _ _ _ hNZ hNV hNH
  (spherical_frame_cone e) F L 0%N hL (hSmooth 0%N).
have hNOpen:=@norm_class_zero_domain_open R Z H _ _ hNZ N
  (fun x=>F (L x)) (norm_class_continuous hNClass).
have hgN:N (pH g).
  change (spherical_frame_cone e (euclidean_rectangular_adjoint g (eH (pH g) (e ord0)))).
  rewrite (finite_inner_chart_right_inverse hChart); exact hgU.
have hPoint:(pH @` S') (pH g) by exists g.
have [T [C [sigma [tau [W hStraight]]]]]:=hS'Man (pH g) hPoint.
apply:(@submanifold_straightening_local_agreement R d (r+n*(n-1)%/2)%N k
  (pH @` S) (pH @` S') N T C (pH g) sigma tau W hStraight hNOpen hgN).
move=>x hx; split.
- move=>[a ha hpa]; exists a; last exact hpa.
  split; first exact ha.1.
  split; first exact ha.2.
  change (spherical_frame_cone e (L x)) in hx.
  rewrite -hpa in hx.
  change (spherical_frame_cone e (euclidean_rectangular_adjoint g (eH (pH a) (e ord0)))) in hx.
  by rewrite (finite_inner_chart_right_inverse hChart) in hx.
- move=>[a ha hpa]; exists a; last exact hpa.
  exact (conj ha.1 ha.2.1).
Qed.

(** Source for [spherical_orthogonal_preimage_submanifold]: the
    same actual preimage assertion for every original unit c,
    3.2.47, p. 283. An orthonormal basis starting
    with c is proved to exist and stays local. *)
Theorem spherical_orthogonal_preimage_submanifold (R:realType) n r k
    (c:R_n R n.+1) (E:set (R_n R n.+1)):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  (1<=k)%N ->@is_euclidean_submanifold R n.+1 r k E ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  is_inner_submanifold (@euclidean_hom_inner_product R n.+1 n.+1)
    (r+n*(n-1)%/2)%N k (spherical_orthogonal_preimage c E).
Proof.
move=>hc hk hMan hSphere.
have [e [he [hON hFirst]]]:=@spherical_base_point_basis_exists R n c hc.
have hResult:=@spherical_basis_preimage_submanifold R n r k e he hON E hk hMan hSphere.
by rewrite hFirst in hResult.
Qed.
