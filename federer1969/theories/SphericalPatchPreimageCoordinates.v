(** Federer (1969), 3.2.47, p. 283: on a translated
    printed patch, the actual preimage of a class-k
    submanifold has local product coordinates of dimension r+mu.
    Section, smoothness, whole isotropy and both inverse laws
    are proved for the original orthogonal operators. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerConvex HilbertFormCompactness ProductInner
  LinearBasis OrthonormalFamilies OrthogonalMaps InnerNormalization
  EuclideanHomInnerCharts EuclideanRectangularAdjoint NormDifferentialUP
  NormRegularity NormRegularityOperations NormCoordinateSystemUP
  FiniteInnerSubmanifoldUP FiniteInnerSmoothSubmanifoldUP FiniteInnerSubmanifoldCoordinates
  EuclideanBlockCoordinates EuclideanCartesianMap EuclideanCartesianConvexGeometry
  SphericalOrthogonalSectionUP SphericalOrthogonalProductAlgebra SphericalOrthogonalProductChart
  SphericalOrthogonalProductSmooth SphericalOrthogonalOrbitDifferential
  SphericalProductPreimageImage SphericalIsotropySmoothSubmanifold ProductChartPullbackCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_patch_preimage_coordinates]: the actual
    local coordinates implicit in the last paragraph of
    3.2.47, p. 283. The original E may be
    noncompact; only its containment in this local translated
    patch is used. The resulting exact image retains E. *)
Theorem spherical_patch_preimage_coordinates (R:realType) n r k
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e)
    (hON:orthonormal_family (@euclidean_inner_product R n.+1) e)
    (t:Hom (R_n R n.+1) (R_n R n.+1)) (E:set (R_n R n.+1))
    (g:Hom (R_n R n.+1) (R_n R n.+1)):
  is_orthogonal_map (@euclidean_inner_product R n.+1)
    (@euclidean_inner_product R n.+1) (hom_as_linear t) ->
  (forall a,E a ->spherical_frame_patch e (euclidean_rectangular_adjoint t a)) ->
  is_inner_submanifold (@euclidean_inner_product R n.+1) r k E ->
  spherical_orthogonal_preimage (e ord0) E g ->
  exists T Q phi psi,
    norm_domain_interior (inner_norm (@euclidean_hom_inner_productP R n.+1 n.+1)) T g /\
    is_inner_convex Q /\
    is_norm_coordinate_system
      (inner_norm_real_norm (@euclidean_hom_inner_productP R n.+1 n.+1))
      (inner_norm_real_norm (@euclidean_inner_productP R (r+n*(n-1)%/2)))
      (spherical_orthogonal_preimage (e ord0) E) T Q phi psi k.
Proof.
move=>ht hE hMan hg.
pose V:=R_n R n.+1.
pose H:=Hom V V.
pose hV:=@euclidean_inner_productP R n.+1.
pose hH:=@euclidean_hom_inner_productP R n.+1 n.+1.
pose hNV:=inner_norm_real_norm hV.
pose hNH:=inner_norm_real_norm hH.
pose mu:=(n*(n-1)%/2)%N.
pose I0:=spherical_orthogonal_isotropy (e ord0).
have hc:inner_norm hV (e ord0)= 1.
  exact (@orthonormal_norm1 R V (@euclidean_inner_product R n.+1) hV
    (Finite.clone 'I_n.+1 _) e hON ord0).
have hIMan:is_inner_submanifold (@euclidean_hom_inner_product R n.+1 n.+1) mu k I0.
  exact (inner_smooth_submanifold_class (@spherical_isotropy_smooth_submanifold R n (e ord0) hc) k).
have [F [hSmooth [hForward hBackward]]]:=
  @spherical_orthogonal_product_chart_exists R n e he hON t ht.
pose D:=fun x:H=>spherical_frame_cone e (euclidean_rectangular_adjoint t (x (e ord0))).
pose h:=fun x:H=>spherical_section_product_coordinate t
  (F (euclidean_rectangular_adjoint t (x (e ord0)))) x.
pose j:=fun z:V*H=>spherical_section_product_inverse t
  (F (euclidean_rectangular_adjoint t z.1)) z.2.
pose B:=fun z:V*H=>spherical_frame_cone e (euclidean_rectangular_adjoint t z.1).
have hh:norm_class hNH hNH D h k.
  exact (@spherical_product_coordinate_smooth R n e F hSmooth t k).
have hj:norm_class
    (inner_norm_real_norm (product_inner_productP hV hH)) hNH B j k.
  exact (@spherical_product_inverse_smooth R n e F hSmooth t k).
have hOpen x (hx:D x):norm_domain_interior (inner_norm hH) D x.
  exact ((@norm_class_continuous R H H _ _ hNH hNH D h k hh x hx).1).
have hp:norm_class hNH hNV D (spherical_orthogonal_orbit (e ord0)) k.
  exact (@norm_class_open_restriction R H V _ _ hNH hNV setT D
    (spherical_orthogonal_orbit (e ord0)) k (fun x _=>I) hOpen
    (@spherical_orthogonal_orbit_smooth R n.+1 (e ord0) k)).
have hgD:D g:= (hE _ hg.2).2.
have hgI:I0 (h g):=(hForward g hg.1 (hE _ hg.2)).1.
have [TE [QE [phiE [psiE [hTE [hQE hCE]]]]]]:=
  @finite_inner_submanifold_coordinates R V _ hV r k E (g (e ord0)) hMan hg.2.
have [TI [QI [phiI [psiI [hTI [hQI hCI]]]]]]:=
  @finite_inner_submanifold_coordinates R H _ hH mu k I0 (h g) hIMan hgI.
pose A:=fun x:H=> (D x /\TE (x (e ord0))) /\(D x /\TI (h x)).
pose Q:=euclidean_cartesian_set QE QI.
pose phi:=fun x:H=>euclidean_block_join (phiE (x (e ord0)),phiI (h x)).
pose psi:=fun z:R_n R (r+mu)=>j (psiE (euclidean_block_split z).1,psiI (euclidean_block_split z).2).
have hDomain a b (ha:E a) (hb:I0 b):B (a,b):=(hE a ha).2.
have hFwd x (hx:spherical_orthogonal_preimage (e ord0) E x) (hxD:D x):
    E (x (e ord0)) /\I0 (h x) /\j (x (e ord0),h x)=x.
  have [hIx hJx]:=hForward x hx.1 (hE _ hx.2).
  exact (conj hx.2 (conj hIx hJx)).
have hBwd a b (ha:E a) (hb:I0 b):
    spherical_orthogonal_preimage (e ord0) E (j (a,b)) /\
    j (a,b) (e ord0)=a /\D (j (a,b)) /\h (j (a,b))=b.
  have [hOrth [hValue [hPatch hCoordinate]]]:=hBackward a b (hE a ha) hb.
  split.
  + split; first exact hOrth.
    change (E (j (a,b) (e ord0))); by rewrite hValue.
  + exact (conj hValue (conj hPatch.2 hCoordinate)).
have hCoordinates:is_norm_coordinate_system hNH
    (inner_norm_real_norm (@euclidean_inner_productP R (r+mu)))
    (spherical_orthogonal_preimage (e ord0) E) A Q phi psi k.
  exact (@product_chart_pullback_coordinates R H V H _ _ _ hH hV hH
    (spherical_orthogonal_preimage (e ord0) E) D E I0 B
    (spherical_orthogonal_orbit (e ord0)) h j r mu k TE TI QE QI phiE psiE phiI psiI
    hCE hCI hp hh hj hDomain hFwd hBwd).
have hgA:A g.
  exact (conj (conj hgD (norm_domain_interior_member hNV hTE))
    (conj hgD (norm_domain_interior_member hNH hTI))).
exists A,Q,phi,psi; split.
- exact ((@norm_class_continuous R H (R_n R (r+mu)) _ _ hNH
    (inner_norm_real_norm (@euclidean_inner_productP R (r+mu))) A phi k
    (norm_coordinate_class_forward hCoordinates) g hgA).1).
- split; last exact hCoordinates.
  exact (euclidean_cartesian_convex hQE hQI).
Qed.
