(** Federer (1969), 3.2.48, pp. 284, 286: the
    whole-preimage mass formula of 3.2.47(3) gives the actual
    pushforward identity used to transport the printed weights.
    The equality is on all sets, including nonmeasurable tests. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts UnitSphereSpace SphericalProductPreimageImage SphericalOrthogonalProductAlgebra
  SphericalFinitePullback SphericalOrthogonalMass SphericalIsotropyMeasure
  RectifiableSetUP MeasureRectifiableSubset HausdorffMeasure MeasureRestriction MeasurePushforward
  MeasureScaleIntegral RealPowerHalfNatural StiefelGammaVolumeScalar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_preimage_mass_scale]: the finite
    positive scalar 2^(r/2) H^mu(I) in 3.2.47(3),
    p. 283, used for the weight integrals of 3.2.48,
    pp. 284, 286. Its isotropy factor is the actual
    3.2.28(5) Gamma value, including n=0. *)
Definition spherical_preimage_mass_scale (R:realType) n r:R:=
  (Num.sqrt (2:R))^+r*stiefel_gamma_volume_scalar R (leqnn n).

(** Source for [spherical_preimage_mass_scale_positive]: the
    scalar used in the original weight transports is strictly
    positive, supporting 3.2.48, pp. 284, 286. *)
Lemma spherical_preimage_mass_scale_positive (R:realType) n r:
  0<spherical_preimage_mass_scale R n r.
Proof.
apply:mulr_gt0; last exact:stiefel_gamma_volume_scalar_positive.
apply:exprn_gt0; by rewrite sqrtr_gt0 ltr0n.
Qed.

(** Source for [spherical_pullback_pushforward]: the exact
    restricted image-measure identity underlying the two weighted
    applications of 3.2.47(3) in 3.2.48, pp. 284,
    286. Original E need not be Borel or measurable for
    this equality of outer measures on all target tests. *)
Theorem spherical_pullback_pushforward (R:realType) n r
    (c:R_n R n.+1) (E:set (R_n R n.+1)):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n.+1)) r) r E ->
  measure_pushforward (fun g:Hom (R_n R n.+1) (R_n R n.+1)=>g c)
    (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) (r+n*(n-1)%/2)%N)
      (spherical_orthogonal_preimage c E))=
  measure_scale (spherical_preimage_mass_scale R n r)
    (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n.+1)) r) E).
Proof.
move=>hc hES hRect; apply:funext=>A.
pose X:=inner_metric_space (@euclidean_inner_productP R n.+1).
pose Y:=inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1).
pose rho:=@hausdorff_measure R Y (r+n*(n-1)%/2)%N.
have hEA:E `&` A `<=` @euclidean_unit_sphere_set R n.+1.
  move=>a ha; exact (hES a ha.1).
have hRectEA:=@measure_rectifiable_subset R X (@hausdorff_measure R X r) r E (E `&` A)
  (fun a ha=>ha.1) hRect.
have hPreRect:=@spherical_finite_rectifiable_pullback R n r c (E `&` A) hc hEA hRectEA.
have hMass:=(@federer_3_2_47_3 R n c (E `&` A) r hc hEA hPreRect).2.
have hSet:spherical_orthogonal_preimage c E `&` (fun g=>g c) @^-1` A=
    spherical_orthogonal_preimage c (E `&` A).
  apply/seteqP; split=>g; first by move=>[[hg hE] hA]; split; last split.
  by move=>[hg [hE hA]]; split; first split.
rewrite /measure_pushforward /measure_restrict hSet hMass
  (@spherical_isotropy_gamma_mass R n c hc)
  (@real_power_half_natural R 2 r ltac:(by rewrite ltr0n)) -EFinM.
reflexivity.
Qed.
