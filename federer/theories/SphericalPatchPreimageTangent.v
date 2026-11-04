(** Federer (1969), 3.2.47, p. 283: exact tangent
    geometry of the original preimage over a class-one
    submanifold in one translated printed patch. Local coordinate
    retractions and the actual product inverse prove the tangent
    equality; no horizontal or vertical containment is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerNorm InnerNormalization HilbertFormCompactness ProductInner LinearBasis OrthonormalFamilies
  OrthogonalMaps EuclideanHomInnerCharts EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  NormDifferentialUP NormDifferentialLocal NormClassOneUP NormRegularity NormCoordinateSystemUP
  RetractionUP FiniteInnerSubmanifoldUP FiniteInnerSmoothSubmanifoldUP FiniteInnerSubmanifoldCoordinates
  TangentConeUP ProductChartPullbackTangent SphericalOrthogonalSectionUP
  SphericalOrthogonalProductAlgebra SphericalOrthogonalProductChart SphericalOrthogonalProductSmooth
  SphericalOrthogonalOrbitDifferential SphericalProductPreimageImage SphericalIsotropySmoothSubmanifold.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_patch_preimage_tangent]: the actual
    inverse-image tangent identity used to calculate Jr Phi,
    3.2.47, p. 283. The original E, all
    tangent vectors, and the Hilbert Hom norm are retained;
    auxiliary coordinate retractions stay local witnesses. *)
Theorem spherical_patch_preimage_tangent (R:realType) n r
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e)
    (hON:orthonormal_family (@euclidean_inner_product R n.+1) e)
    (t:Hom (R_n R n.+1) (R_n R n.+1)) (E:set (R_n R n.+1))
    (g:Hom (R_n R n.+1) (R_n R n.+1)):
  is_orthogonal_map (@euclidean_inner_product R n.+1)
    (@euclidean_inner_product R n.+1) (hom_as_linear t) ->
  (forall a,E a ->spherical_frame_patch e (euclidean_rectangular_adjoint t a)) ->
  is_inner_submanifold (@euclidean_inner_product R n.+1) r 1%N E ->
  spherical_orthogonal_preimage (e ord0) E g ->
  norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
    (spherical_orthogonal_preimage (e ord0) E) g=
  [set w|norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
    [set x|is_orthogonal_map (@euclidean_inner_product R n.+1)
      (@euclidean_inner_product R n.+1) (hom_as_linear x)] g w /\
    norm_tangent_cone (inner_norm (@euclidean_inner_productP R n.+1)) E (g (e ord0)) (w (e ord0))].
Proof.
move=>ht hE hMan hg.
pose V:=R_n R n.+1.
pose H:=Hom V V.
pose hV:=@euclidean_inner_productP R n.+1.
pose hH:=@euclidean_hom_inner_productP R n.+1 n.+1.
pose hNV:=inner_norm_real_norm hV.
pose hNH:=inner_norm_real_norm hH.
pose hNP:=inner_norm_real_norm (product_inner_productP hV hH).
pose P:lmodType R:=[the lmodType R of (V*H)%type].
pose O:set H:=[set x|is_orthogonal_map (@euclidean_inner_product R n.+1)
  (@euclidean_inner_product R n.+1) (hom_as_linear x)].
pose I0:=spherical_orthogonal_isotropy (e ord0).
have hc:inner_norm hV (e ord0)= 1.
  exact (@orthonormal_norm1 R V (@euclidean_inner_product R n.+1) hV
    (Finite.clone 'I_n.+1 _) e hON ord0).
have hIMan:is_inner_submanifold (@euclidean_hom_inner_product R n.+1 n.+1)
    (n*(n-1)%/2)%N 1%N I0.
  exact (inner_smooth_submanifold_class (@spherical_isotropy_smooth_submanifold R n (e ord0) hc) 1%N).
have [F [hSmooth [hForward hBackward]]]:=
  @spherical_orthogonal_product_chart_exists R n e he hON t ht.
pose D:=fun x:H=>spherical_frame_cone e (euclidean_rectangular_adjoint t (x (e ord0))).
pose h:=fun x:H=>spherical_section_product_coordinate t
  (F (euclidean_rectangular_adjoint t (x (e ord0)))) x.
pose j:=fun z:P=>spherical_section_product_inverse t (F (euclidean_rectangular_adjoint t z.1)) z.2.
pose B:=fun z:P=>spherical_frame_cone e (euclidean_rectangular_adjoint t z.1).
have hClassH:norm_class hNH hNH D h 1%N.
  exact (@spherical_product_coordinate_smooth R n e F hSmooth t 1%N).
have hClassJ:norm_class hNP hNH B j 1%N.
  exact (@spherical_product_inverse_smooth R n e F hSmooth t 1%N).
have hgD:D g:=(hE _ hg.2).2.
have hgI:I0 (h g):=(hForward g hg.1 (hE _ hg.2)).1.
have [TE [QE [phiE [psiE [hTE [_ hCE]]]]]]:=
  @finite_inner_submanifold_coordinates R V _ hV r 1%N E (g (e ord0)) hMan hg.2.
have [TI [QI [phiI [psiI [hTI [_ hCI]]]]]]:=
  @finite_inner_submanifold_coordinates R H _ hH (n*(n-1)%/2)%N 1%N I0 (h g) hIMan hgI.
pose re:=fun a=>psiE (phiE a).
pose ri:=fun a=>psiI (phiI a).
have hRE:=norm_coordinate_system_retraction hCE.
have hRI:=norm_coordinate_system_retraction hCI.
have [DE hDE]:=(@norm_class_firstP R V V _ _ hNV hNV TE re).1 (norm_retraction_class hRE).
have [DI hDI]:=(@norm_class_firstP R H H _ _ hNH hNH TI ri).1 (norm_retraction_class hRI).
have [DH hDH]:=(@norm_class_firstP R H H _ _ hNH hNH D h).1 hClassH.
have [DJ hDJ]:=(@norm_class_firstP R P H _ _ hNP hNH B j).1 hClassJ.
have hp:has_norm_differential (inner_norm hH) (inner_norm hV) D
    (spherical_orthogonal_orbit (e ord0)) g (spherical_orthogonal_orbit (e ord0)).
  apply:(@norm_differential_restrict R H V _ _ setT D _ g _ (fun x _=>I)).
  - exact ((@norm_class_continuous R H H _ _ hNH hNH D h 1%N hClassH g hgD).1).
  - exact (@spherical_orthogonal_orbit_differential R n.+1 (e ord0) g).
have hPatch x (hx:O x) (hxD:D x):
    spherical_frame_patch e (euclidean_rectangular_adjoint t (x (e ord0))).
  split; last exact hxD.
  rewrite (orthogonal_map_norm hV hV (euclidean_orthogonal_adjoint_orthogonal ht))
    (orthogonal_map_norm hV hV hx); exact hc.
have hHMap x (hx:O x) (hxD:D x):I0 (h x).
  exact (hForward x hx (@hPatch x hx hxD)).1.
have hInverse x (hx:O x) (hxD:D x):j (x (e ord0),h x)=x.
  exact (hForward x hx (@hPatch x hx hxD)).2.
have hProduct a b (ha:E a) (hb:I0 b):B (a,b) /\spherical_orthogonal_preimage (e ord0) E (j (a,b)).
  split; first exact (hE a ha).2.
  have [hO [hValue _]]:=hBackward a b (hE a ha) hb.
  split; first exact hO.
  change (E (j (a,b) (e ord0))); by rewrite hValue.
exact (@product_chart_pullback_tangent R H V H _ _ _ hH hV hH
  O (spherical_orthogonal_preimage (e ord0) E) D E TE I0 TI B
  (spherical_orthogonal_orbit (e ord0)) h j re ri g (spherical_orthogonal_orbit (e ord0))
  (DH g) (DJ (g (e ord0),h g)) (DE (g (e ord0))) (DI (h g))
  (fun x=>iff_refl _) hg hgD hp (norm_class_one_differential hDH hgD)
  (@norm_class_one_differential R P H _ _ B j DJ hDJ (g (e ord0),h g) hgD)
  (norm_class_one_differential hDE (norm_domain_interior_member hNV hTE))
  (norm_class_one_differential hDI (norm_domain_interior_member hNH hTI))
  hHMap (fun x hx=>hx) hInverse hProduct
  (fun a ha=>(norm_retraction_range hRE ha).1)
  (fun a ha=>(norm_retraction_range hRI ha).1)
  (fun a ha ht=>norm_retraction_fixed hRE (conj ha ht))
  (fun a ha ht=>norm_retraction_fixed hRI (conj ha ht))).
Qed.
