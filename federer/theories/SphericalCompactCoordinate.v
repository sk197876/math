(** Federer (1969), 3.2.47(3), p. 283: the actual
    H_e is Lipschitz on the whole preimage of a compact
    base core inside e(U). Its full I fibres map
    back onto the original E by Phi. All auxiliary
    representatives and bounds are proved locally. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric HilbertFormCompactness OrthogonalMaps
  LinearBasis OrthonormalFamilies EuclideanHomInnerCharts EuclideanRectangularAdjoint
  NormClassOneUP NormRegularity SphericalOrthogonalSectionUP
  SphericalOrthogonalProductAlgebra SphericalOrthogonalProductChart
  SphericalOrthogonalProductSmooth SphericalProductPreimageImage SphericalOrbitCompactness
  InnerClassOneCompactLipschitz LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_compact_coordinate_exists]: the
    actual H_e on a compact preimage, with its proved
    finite Lipschitz bound, I-valued range and complete
    original E fibres, as required in the converse proof
    of 3.2.47(3), p. 283. *)
Theorem spherical_compact_coordinate_exists (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e)
    (hON:orthonormal_family (@euclidean_inner_product R n.+1) e)
    (t:Hom (R_n R n.+1) (R_n R n.+1)) (K:set (R_n R n.+1)):
  is_orthogonal_map (@euclidean_inner_product R n.+1)
    (@euclidean_inner_product R n.+1) (hom_as_linear t) ->
  @compact (inner_metric_space (@euclidean_inner_productP R n.+1)) K ->
  (forall a,K a ->spherical_frame_patch e (euclidean_rectangular_adjoint t a)) ->
  exists H0:Hom (R_n R n.+1) (R_n R n.+1)->Hom (R_n R n.+1) (R_n R n.+1),
    @is_metric_lipschitz R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
      (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
      (spherical_orthogonal_preimage (e ord0) K) H0 /\
    (forall g,spherical_orthogonal_preimage (e ord0) K g ->
      spherical_orthogonal_isotropy (e ord0) (H0 g)) /\
    forall (E:set (R_n R n.+1)) h,E `<=` K ->spherical_orthogonal_isotropy (e ord0) h ->
      forall a,E a ->exists g,spherical_orthogonal_preimage (e ord0) E g /\
        H0 g=h /\g (e ord0)=a.
Proof.
move=>ht hK hPatch.
pose V:=R_n R n.+1.
pose H:=Hom V V.
pose hH:=@euclidean_hom_inner_productP R n.+1 n.+1.
have [F [hF [hForward hBackward]]]:=@spherical_orthogonal_product_chart_exists R n e he hON t ht.
pose H0:=fun g:H=>spherical_section_product_coordinate t
  (F (euclidean_rectangular_adjoint t (g (e ord0)))) g.
pose A:=fun g:H=>spherical_frame_cone e (euclidean_rectangular_adjoint t (g (e ord0))).
have hClass:norm_class_one (inner_norm hH) (inner_norm hH) A H0.
  exact ((@norm_class_firstP R H H (inner_norm hH) (inner_norm hH)
    (inner_norm_real_norm hH) (inner_norm_real_norm hH) A H0).1
    (@spherical_product_coordinate_smooth R n e F hF t 1%N)).
have hDomain:spherical_orthogonal_preimage (e ord0) K `<=` A.
  move=>g hg; exact:(hPatch _ hg.2).2.
have hCompact:=@spherical_orthogonal_preimage_compact R n.+1 (e ord0) K hK.
have hLip:=@inner_class_one_compact_lipschitz R H H _ _ hH hH A
  (spherical_orthogonal_preimage (e ord0) K) H0 hClass hDomain hCompact.
exists H0; split; first exact hLip.
split.
- move=>g [hg hKg]; exact:(hForward g hg (hPatch _ hKg)).1.
- move=>E h hEK hI a ha.
  pose g:=spherical_section_product_inverse t (F (euclidean_rectangular_adjoint t a)) h.
  have [hg [hValue [hInside hCoordinate]]]:=hBackward a h (hPatch _ (hEK a ha)) hI.
  exists g; split.
  + split; first exact hg.
    by rewrite /g hValue.
  + split; last exact hValue.
    exact hCoordinate.
Qed.
