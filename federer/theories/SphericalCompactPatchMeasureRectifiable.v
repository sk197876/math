(** Federer (1969), 3.2.47(1),(2), p. 283: finite-mass
    rectifiability of the original Phi preimage on
    one compact base core inside a fixed translated patch.
    Compact core times the whole isotropy is compact; finite
    local Lipschitz refinements of the actual smooth inverse
    chart prove finiteness for the original Borel source. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNormalization InnerNorm InnerMetric HilbertFormCompactness
  OrthogonalMaps LinearBasis OrthonormalFamilies EuclideanHomInnerCharts
  EuclideanRectangularAdjoint ProductInner FiniteInnerChartUP FiniteInnerCartesianTransfer
  NormClassOneUP NormRegularity SphericalOrthogonalSectionUP
  SphericalOrthogonalProductAlgebra SphericalOrthogonalProductSmooth
  SphericalProductPreimageImage SphericalIsotropyRectifiable
  InnerClassOneCompactImages InnerClassOneCompactLipschitz FiniteMeasureRectifiableImages
  FiniteInnerRectifiableCartesianProduct RectifiableSetUP HausdorffMeasure TopologicalBorel
  LipschitzUP LipschitzBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_compact_patch_measure_rectifiable]:
    finite-mass rectifiability of the original preimage on
    a compact base patch, supporting 3.2.47(3), p. 283.
    Actual 3.2.23 applies with the whole compact isotropy
    as the genuine factor; the source E need only
    have finite Hausdorff rectifiability and be Borel. *)
Theorem spherical_compact_patch_measure_rectifiable (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e)
    (hON:orthonormal_family (@euclidean_inner_product R n.+1) e)
    (t:Hom (R_n R n.+1) (R_n R n.+1)) (K E:set (R_n R n.+1)) r:
  is_orthogonal_map (@euclidean_inner_product R n.+1)
    (@euclidean_inner_product R n.+1) (hom_as_linear t) ->
  @compact (inner_metric_space (@euclidean_inner_productP R n.+1)) K ->
  (forall a,K a ->spherical_frame_patch e (euclidean_rectangular_adjoint t a)) ->
  E `<=` K ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n.+1)) r) r E ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n.+1)) E ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
      (r+n*(n-1)%/2)%N) (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage (e ord0) E).
Proof.
move=>ht hK hPatch hEK hE hEB.
pose V:=R_n R n.+1.
pose H:=Hom V V.
pose hV:=@euclidean_inner_productP R n.+1.
pose hH:=@euclidean_hom_inner_productP R n.+1 n.+1.
pose hP:=product_inner_productP hV hH.
pose I0:=spherical_orthogonal_isotropy (e ord0).
have hc:inner_norm hV (e ord0)= 1.
  exact (@orthonormal_norm1 R V (@euclidean_inner_product R n.+1) hV
    (Finite.clone 'I_n.+1 _) e hON ord0).
have [hICompact hIRect]:=@spherical_isotropy_compact_rectifiable R n (e ord0) hc.
have [f [p hChart]]:=@euclidean_hom_inner_chart_exists R n.+1 n.+1.
pose idV:Hom V V:=hom_of_linear (linear_id V).
have hIdentity:is_finite_inner_chart (@euclidean_inner_product R n.+1) idV idV.
  constructor; [by move=>x|by move=>x|by move=>x y].
have hProductCompact:=@finite_inner_cartesian_compact R V H _ _ hV hH
  n.+1 (n.+1*n.+1)%N idV idV f p hIdentity hChart K I0 hK hICompact.
have [F [hF hImages]]:=@spherical_product_preimage_image_exists R n e he hON t ht.
pose A:=fun z:V*H=>spherical_frame_cone e (euclidean_rectangular_adjoint t z.1).
pose J:=fun z:V*H=>spherical_section_product_inverse t (F (euclidean_rectangular_adjoint t z.1)) z.2.
have hJ:norm_class_one (inner_norm hP) (inner_norm hH) A J.
  exact ((@norm_class_firstP R [the lmodType R of (V*H)%type] H
    (inner_norm hP) (inner_norm hH) (inner_norm_real_norm hP) (inner_norm_real_norm hH)
    A J).1 (@spherical_product_inverse_smooth R n e F hF t 1%N)).
have hDomain:[set z:V*H|K z.1 /\I0 z.2] `<=` A.
  by move=>z hz; exact:(hPatch z.1 hz.1).2.
have hSubset:[set z:V*H|E z.1 /\I0 z.2] `<=` [set z:V*H|K z.1 /\I0 z.2].
  move=>z hz; split; first exact:hEK z.1 hz.1.
  exact hz.2.
have hImage:=hImages E (fun a ha=>hPatch a (hEK a ha)).
have hIB:@borel_set (inner_metric_space hH) I0.
  apply:closed_borel_set.
  exact (compact_closed (@metric_hausdorff R (inner_metric_space hH)) hICompact).
have hProduct:=@finite_inner_rectifiable_cartesian_product_right R V H _ _ hV hH
  n.+1 (n.+1*n.+1)%N idV idV f p r (n*(n-1)%/2)%N E I0
  hIdentity hChart hE hEB hIRect hIB.
have [L [hL hBound]]:=@inner_class_one_compact_lipschitz R [the lmodType R of (V*H)%type] H
  _ _ hP hH A [set z:V*H|K z.1 /\I0 z.2] J hJ hDomain hProductCompact.
have hLip:@is_metric_lipschitz R (inner_metric_space hP) (inner_metric_space hH)
    [set z:V*H|E z.1 /\I0 z.2] J.
  exists L; split; first exact hL.
  exact (@metric_lipschitz_bound_restrict R (inner_metric_space hP) (inner_metric_space hH)
    [set z:V*H|K z.1 /\I0 z.2] [set z:V*H|E z.1 /\I0 z.2] J L hSubset hBound).
have hResult:=hausdorff_measure_rectifiable_lipschitz_image hLip hProduct.
by rewrite hImage in hResult.
Qed.
