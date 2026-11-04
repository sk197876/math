(** Federer (1969), 3.2.47, p. 283: the tangent
    inverse-image identity for the whole original E. Actual
    open translated patches retain both original tangents by
    locality. No extra local chart or derivative premise
    remains in the final geometric theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies OrthogonalMaps PartialFunctionUP
  EuclideanHomInnerCharts EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  FiniteInnerChartUP FiniteInnerSubmanifoldUP EuclideanSubmanifoldUP SubmanifoldOpenRestriction
  NormDifferentialUP NormRegularity NormRegularityLinearMaps NormFiniteLinearBound
  TangentConeUP TangentConeLocal UnitSphereSpace
  SphericalOrthogonalSectionUP SphericalOrthogonalSection SphericalOrthogonalSectionValues
  SphericalOrthogonalProductAlgebra SphericalOrthogonalProductChart SphericalOrthogonalProductSmooth SphericalBasePointBasis
  SphericalProductPreimageImage SphericalPatchPreimageTangent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_preimage_patch_restriction]: the local
    reduction to a printed translated patch in 3.2.47,
    p. 283, with both ORIGINAL tangent cones preserved.
    Restrict E before choosing its convex coordinate chart;
    no parameter domain is silently assumed convex after shrinking. *)
Lemma spherical_preimage_patch_restriction (R:realType) n r k
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e)
    (hON:orthonormal_family (@euclidean_inner_product R n.+1) e)
    (E:set (R_n R n.+1)) (g:Hom (R_n R n.+1) (R_n R n.+1)):
  @is_euclidean_submanifold R n.+1 r k E ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  spherical_orthogonal_preimage (e ord0) E g ->
  exists E':set (R_n R n.+1),
    is_inner_submanifold (@euclidean_inner_product R n.+1) r k E' /\
    (forall a,E' a ->spherical_frame_patch e (euclidean_rectangular_adjoint g a)) /\
    spherical_orthogonal_preimage (e ord0) E' g /\
    norm_tangent_cone (inner_norm (@euclidean_inner_productP R n.+1)) E' (g (e ord0))=
      norm_tangent_cone (inner_norm (@euclidean_inner_productP R n.+1)) E (g (e ord0)) /\
    norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
      (spherical_orthogonal_preimage (e ord0) E') g=
    norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
      (spherical_orthogonal_preimage (e ord0) E) g.
Proof.
move=>hMan hSphere hg.
pose V:=R_n R n.+1.
pose H:=Hom V V.
pose hV:=@euclidean_inner_productP R n.+1.
pose hH:=@euclidean_hom_inner_productP R n.+1 n.+1.
pose hNV:=inner_norm_real_norm hV.
pose hNH:=inner_norm_real_norm hH.
have [F [hSmooth _]]:=@spherical_orthogonal_product_chart_exists R n e he hON g hg.1.
pose U:=fun a:V=>spherical_frame_cone e (euclidean_rectangular_adjoint g a).
have hAdj:=@norm_finite_linear_bounded R V V _ _ hNV hNV n.+1
  (@coordinate_basis R n.+1) (@coordinate_basisP R n.+1) (euclidean_rectangular_adjoint g).
have hUClass:=@norm_class_precompose_linear R V V H _ _ _ hNV hNV hNH
  (spherical_frame_cone e) F (euclidean_rectangular_adjoint g) 0%N hAdj (hSmooth 0%N).
have hUOpen:=@NormClassZeroTopology.norm_class_zero_domain_open R V H _ _ hNV U
  (fun a=>F (euclidean_rectangular_adjoint g a)) (norm_class_continuous hUClass).
pose E':=E `&` U.
have hEMan:=@euclidean_submanifold_open_restriction R n.+1 r k E U hMan hUOpen.
have hInnerMan:is_inner_submanifold (@euclidean_inner_product R n.+1) r k E'.
  pose idV:Hom V V:=hom_of_linear (linear_id V).
  have hId:is_finite_inner_chart (@euclidean_inner_product R n.+1) idV idV by constructor.
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
pose D:=fun x:H=>U (x (e ord0)).
have hDClass:=@spherical_product_coordinate_smooth R n e F hSmooth g 0%N.
have hDEq:spherical_orthogonal_preimage (e ord0) E'=
    spherical_orthogonal_preimage (e ord0) E `&` D.
  apply/seteqP; split=>x.
  - move=>[hx [hxE hxU]]; exact (conj (conj hx hxE) hxU).
  - move=>[[hx hxE] hxU]; exact (conj hx (conj hxE hxU)).
exists E'; split; first exact hInnerMan.
split; first exact hE'Patch.
split; first exact (conj hg.1 (conj hg.2 hgU)).
split.
- exact (@norm_tangent_open_restriction R V (inner_norm hV) E U (g (e ord0))
    ((@norm_class_continuous R V H _ _ hNV hNH U
      (fun a=>F (euclidean_rectangular_adjoint g a)) 0%N hUClass (g (e ord0)) hgU).1)).
- rewrite hDEq.
  exact (@norm_tangent_open_restriction R H (inner_norm hH)
    (spherical_orthogonal_preimage (e ord0) E) D g
    ((@norm_class_continuous R H H _ _ hNH hNH D
      (fun x=>spherical_section_product_coordinate g
        (F (euclidean_rectangular_adjoint g (x (e ord0)))) x) 0%N hDClass g hgU).1)).
Qed.

(** Source for [spherical_basis_preimage_tangent]: the actual
    whole-preimage tangent used in 3.2.47, p. 283,
    expressed in a local orthonormal basis starting with c.
    The only source assumptions are the original class-one
    submanifold and sphere containment. *)
Theorem spherical_basis_preimage_tangent (R:realType) n r
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e)
    (hON:orthonormal_family (@euclidean_inner_product R n.+1) e)
    (E:set (R_n R n.+1)) (g:Hom (R_n R n.+1) (R_n R n.+1)):
  @is_euclidean_submanifold R n.+1 r 1%N E ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  spherical_orthogonal_preimage (e ord0) E g ->
  norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
    (spherical_orthogonal_preimage (e ord0) E) g=
  [set w|norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
    [set x|is_orthogonal_map (@euclidean_inner_product R n.+1)
      (@euclidean_inner_product R n.+1) (hom_as_linear x)] g w /\
    norm_tangent_cone (inner_norm (@euclidean_inner_productP R n.+1)) E (g (e ord0)) (w (e ord0))].
Proof.
move=>hMan hSphere hg.
have [E' [hE'Man [hPatch [hg' [hTanE hTanS]]]]]:=
  @spherical_preimage_patch_restriction R n r 1%N e he hON E g hMan hSphere hg.
have hLocal:=@spherical_patch_preimage_tangent R n r e he hON g E' g
  hg.1 hPatch hE'Man hg'.
by rewrite hTanS hTanE in hLocal.
Qed.

(** Source for [spherical_orthogonal_preimage_tangent]: the actual
    tangent inverse-image identity for every original unit c,
    used in the last display of 3.2.47, p. 283.
    The local orthonormal basis is discharged by existence. *)
Theorem spherical_orthogonal_preimage_tangent (R:realType) n r
    (c:R_n R n.+1) (E:set (R_n R n.+1)) (g:Hom (R_n R n.+1) (R_n R n.+1)):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  @is_euclidean_submanifold R n.+1 r 1%N E ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  spherical_orthogonal_preimage c E g ->
  norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
    (spherical_orthogonal_preimage c E) g=
  [set w|norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
    [set x|is_orthogonal_map (@euclidean_inner_product R n.+1)
      (@euclidean_inner_product R n.+1) (hom_as_linear x)] g w /\
    norm_tangent_cone (inner_norm (@euclidean_inner_productP R n.+1)) E (g c) (w c)].
Proof.
move=>hc hMan hSphere hg.
have [e [he [hON hFirst]]]:=@spherical_base_point_basis_exists R n c hc.
have hg':spherical_orthogonal_preimage (e ord0) E g by rewrite hFirst.
have hResult:=@spherical_basis_preimage_tangent R n r e he hON E g hMan hSphere hg'.
by rewrite hFirst in hResult.
Qed.
