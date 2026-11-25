(** Federer (1969), 3.2.47, pp. 282–283: the
    actual isotropy Hausdorff measure is that of O(n-1).
    Its printed dimension has positive finite mass, including
    the unit zero-dimensional atom, by the proved 3.2.28 volume formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  OrthogonalMaps EuclideanHomInnerCharts SphericalOrthogonalProductAlgebra SphericalIsotropyIsometry
  HausdorffMeasure HausdorffIsometricEmbedding EuclideanManifoldVolumes
  EuclideanStiefelGammaVolume StiefelGammaVolumeScalar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_isotropy_hausdorff_measure]: every
    actual Hausdorff degree of the original I equals
    that of O(n-1), by the isometry stated in
    3.2.47, pp. 282–283. The measures have
    their original ambient Hilbert Hom metrics. *)
Theorem spherical_isotropy_hausdorff_measure (R:realType) n (c:R_n R (1+n)):
  inner_norm (@euclidean_inner_productP R (1+n)) c= 1 ->forall q,
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R (1+n) (1+n))) q
    (spherical_orthogonal_isotropy c)=
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n n)) q
    [set h|is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) (hom_as_linear h)].
Proof.
move=>hc q.
have [F [G [hCancel [hDistance hImage]]]]:=@spherical_isotropy_isometric_parametrization R n c hc.
rewrite -hImage.
apply:(@hausdorff_isometric_embedding_invariance R
  (inner_metric_space (@euclidean_hom_inner_productP R n n))
  (inner_metric_space (@euclidean_hom_inner_productP R (1+n) (1+n))) F G hCancel).
move=>h g; rewrite !inner_metric_distanceE; exact:hDistance.
Qed.

(** Source for [spherical_isotropy_gamma_mass]: the positive
    finite actual H^mu(I) in 3.2.47, p. 283,
    evaluated by 3.2.28(5), p. 267. Here the
    ambient dimension is n+1 and mu=n(n-1)/2;
    no truncated subtraction of the printed dimension is used. *)
Theorem spherical_isotropy_gamma_mass (R:realType) n (c:R_n R (1+n)):
  inner_norm (@euclidean_inner_productP R (1+n)) c= 1 ->
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R (1+n) (1+n)))
    (n*(n-1)%/2)%N (spherical_orthogonal_isotropy c)=
    (stiefel_gamma_volume_scalar R (leqnn n))%:E.
Proof.
move=>hc; rewrite (spherical_isotropy_hausdorff_measure hc).
have hDegree:(n*(2*n-n-1)%/2=n*(n-1)%/2)%N.
  by rewrite mul2n -addnn addKn.
rewrite -hDegree; exact (@euclidean_stiefel_gamma_volume R n n (leqnn n)).
Qed.

(** Source for [spherical_isotropy_mass_positive_finite]: all
    later cancellations of H^mu(I) are justified by
    its actual positivity and finiteness, supporting 3.2.47–48,
    pp. 283–286, including ambient dimension one. *)
Corollary spherical_isotropy_mass_positive_finite (R:realType) n (c:R_n R (1+n)):
  inner_norm (@euclidean_inner_productP R (1+n)) c= 1 ->
  (0<@hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R (1+n) (1+n)))
    (n*(n-1)%/2)%N (spherical_orthogonal_isotropy c))%E /\
  (@hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R (1+n) (1+n)))
    (n*(n-1)%/2)%N (spherical_orthogonal_isotropy c)< +oo)%E.
Proof.
move=>hc; rewrite (spherical_isotropy_gamma_mass hc); split.
- by rewrite lte_fin; exact:stiefel_gamma_volume_scalar_positive.
- by rewrite ltry.
Qed.
