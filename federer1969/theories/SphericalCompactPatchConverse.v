(** Federer (1969), 3.2.47(3), p. 283: the first
    conclusion on a compact base core inside one translated
    patch. All source, target, slicing, positivity and actual
    fibre-image hypotheses of 3.2.22(2) are discharged.
    Arbitrary nonmeasurable original E remains. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNormalization InnerNorm InnerMetric OrthogonalMaps
  LinearBasis OrthonormalFamilies EuclideanHomInnerCharts EuclideanRectangularAdjoint
  SphericalOrthogonalSectionUP SphericalOrthogonalProductAlgebra
  SphericalProductPreimageImage SphericalOrthogonalOrbitDifferential SphericalOrbitCompactness SphericalCompactCoordinate
  SphericalIsotropyRectifiable SphericalIsotropyMeasure FiniteInnerCompactFibreConverse
  RectifiableSetUP RectifiableElementary HausdorffMeasure MeasureUP MeasureBasic MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [spherical_compact_patch_converse]: the
    actual slicing-map argument for the first conclusion of
    3.2.47(3), p. 283, on one compact base core.
    A true Borel hull and positive actual isotropy mass
    replace any assumption of source measurability or null
    hull excess; all natural r are retained. *)
Theorem spherical_compact_patch_converse (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e)
    (hON:orthonormal_family (@euclidean_inner_product R n.+1) e)
    (t:Hom (R_n R n.+1) (R_n R n.+1)) (K E:set (R_n R n.+1)) r:
  is_orthogonal_map (@euclidean_inner_product R n.+1)
    (@euclidean_inner_product R n.+1) (hom_as_linear t) ->
  @compact (inner_metric_space (@euclidean_inner_productP R n.+1)) K ->
  (forall a,K a ->spherical_frame_patch e (euclidean_rectangular_adjoint t a)) ->
  E `<=` K ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) (r+n*(n-1)%/2))
    (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage (e ord0) E) ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n.+1)) r) r E.
Proof.
move=>ht hK hPatch hEK hRect.
pose V:=R_n R n.+1.
pose H:=Hom V V.
pose hH:=@euclidean_hom_inner_productP R n.+1 n.+1.
pose I0:=spherical_orthogonal_isotropy (e ord0).
have hc:inner_norm (@euclidean_inner_productP R n.+1) (e ord0)= 1%R.
  exact (@orthonormal_norm1 R V (@euclidean_inner_product R n.+1)
    (@euclidean_inner_productP R n.+1) (Finite.clone 'I_n.+1 _) e hON ord0).
have [hICompact hIRect]:=@spherical_isotropy_compact_rectifiable R n (e ord0) hc.
have [hIPositive hIFinite]:=@spherical_isotropy_mass_positive_finite R n (e ord0) hc.
have hIMeasureRect:is_measure_m_rectifiable
    (@hausdorff_measure R (inner_metric_space hH) (n*(n-1)%/2)%N) (n*(n-1)%/2)%N I0.
  split; last exact hIFinite.
  split; first exact:hausdorff_measure_is_measure.
  exists I0; split; first exact:rectifiable_countably_rectifiable hIRect.
  by rewrite /measure_almost_included setDv (measure_empty (@hausdorff_measure_is_measure R
    (inner_metric_space hH) (n*(n-1)%/2)%N)).
have [eH [pH hChart]]:=@euclidean_hom_inner_chart_exists R n.+1 n.+1.
have [H0 [hLip [hRange hFibres]]]:=@spherical_compact_coordinate_exists R n e he hON t K ht hK hPatch.
have hCompact:=@spherical_orthogonal_preimage_compact R n.+1 (e ord0) K hK.
have hSubset:spherical_orthogonal_preimage (e ord0) E `<=` spherical_orthogonal_preimage (e ord0) K.
  move=>g hg; split; first exact hg.1.
  exact:hEK _ hg.2.
apply:(@finite_inner_compact_fibre_converse R H H _ _ hH hH
  (n.+1*n.+1)%N (n.+1*n.+1)%N n.+1 r (n*(n-1)%/2)%N eH pH eH pH
  (spherical_orthogonal_preimage (e ord0) K) (spherical_orthogonal_preimage (e ord0) E)
  I0 E H0 (spherical_orthogonal_orbit (e ord0)) hChart hChart hCompact hSubset hICompact
  hRect hIMeasureRect hIPositive hLip hRange
  (@spherical_orthogonal_orbit_lipschitz R n.+1 (e ord0))).
move=>z hz y hy; exact:(hFibres E z hEK hz y hy).
Qed.
