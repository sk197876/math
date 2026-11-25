(** Federer (1969), 3.2.47(1),(2), p. 283: genuine
    rectifiability and nullity of the original Phi preimage on
    one compact base core inside a fixed translated patch.
    Compact core times the whole isotropy is compact; finite
    local Lipschitz refinements of the actual smooth inverse
    chart prove both conclusions for arbitrary original subsets. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNormalization InnerNorm InnerMetric HilbertFormCompactness
  OrthogonalMaps LinearBasis OrthonormalFamilies EuclideanHomInnerCharts
  EuclideanRectangularAdjoint ProductInner FiniteInnerChartUP FiniteInnerCartesianTransfer
  NormClassOneUP NormRegularity SphericalOrthogonalSectionUP
  SphericalOrthogonalProductAlgebra SphericalOrthogonalProductSmooth
  SphericalProductPreimageImage SphericalIsotropyRectifiable
  InnerClassOneCompactImages RectifiableSetUP HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_compact_patch_pullback]: the local
    product proof of both 3.2.47(1) and (2), p. 283.
    All natural r, the whole actual isotropy and nonmeasurable
    original E remain. No global open-patch Lipschitz hypothesis
    or independently supplied bundle is used. *)
Theorem spherical_compact_patch_pullback (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e)
    (hON:orthonormal_family (@euclidean_inner_product R n.+1) e)
    (t:Hom (R_n R n.+1) (R_n R n.+1)) (K E:set (R_n R n.+1)) r:
  is_orthogonal_map (@euclidean_inner_product R n.+1)
    (@euclidean_inner_product R n.+1) (hom_as_linear t) ->
  @compact (inner_metric_space (@euclidean_inner_productP R n.+1)) K ->
  (forall a,K a ->spherical_frame_patch e (euclidean_rectangular_adjoint t a)) ->
  E `<=` K ->
  (@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n.+1)) r E ->
    @is_m_rectifiable R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
      (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage (e ord0) E)) /\
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n.+1)) r E=0%E ->
    @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
      (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage (e ord0) E)=0%E).
Proof.
move=>ht hK hPatch hEK.
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
split.
- move=>hE.
  have hProduct:=@finite_inner_cartesian_rectifiable R V H _ _ hV hH
    n.+1 (n.+1*n.+1)%N idV idV f p hIdentity hChart r (n*(n-1)%/2)%N E I0 hE hIRect.
  have hResult:=@inner_class_one_compact_rectifiable_image R [the lmodType R of (V*H)%type] H
    _ _ hP hH A [set z:V*H|K z.1 /\I0 z.2] [set z:V*H|E z.1 /\I0 z.2]
    J (r+n*(n-1)%/2)%N hJ hDomain hProductCompact hSubset hProduct.
  by rewrite hImage in hResult.
- move=>hE.
  have hProduct:=@finite_inner_cartesian_null R V H _ _ hV hH
    n.+1 (n.+1*n.+1)%N idV idV f p hIdentity hChart r (n*(n-1)%/2)%N E I0 hE hIRect.
  have hResult:=@inner_class_one_compact_null_image R [the lmodType R of (V*H)%type] H
    _ _ hP hH A [set z:V*H|K z.1 /\I0 z.2] [set z:V*H|E z.1 /\I0 z.2]
    J (r+n*(n-1)%/2)%N hJ hDomain hProductCompact hSubset hProduct.
  by rewrite hImage in hResult.
Qed.
