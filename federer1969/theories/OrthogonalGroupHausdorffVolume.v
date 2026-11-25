(** Federer (1969), 3.2.48, p. 284: the actual
    Hausdorff group measure is positive and finite. The
    already proved 3.2.28(5), p. 267, evaluates
    its total mass in the original Hilbert Hom metric. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets functions constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric OrthogonalMaps EuclideanHomInnerCharts OrthogonalGroupHaarMeasure
  EuclideanOrthogonalInvariantMeasures OrthogonalGroupHausdorffCarrier
  HausdorffMeasure EuclideanManifoldVolumes EuclideanStiefelGammaVolume StiefelGammaVolumeScalar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_group_element_full_image]: the actual
    carrier inclusion identifies the whole existing O(N) carrier
    with the orthogonal locus in Hom, 3.2.48, p. 284.
    It retains the unique empty-dimensional orthogonal map. *)
Lemma orthogonal_group_element_full_image (R:realType) N:
  (@orthogonal_element_map R (R_n R N) (@euclidean_inner_product R N)
    (@euclidean_inner_productP R N) N (@coordinate_basis R N) (@coordinate_basisP R N))
    @` (@setT (euclidean_orthogonal_group R N))=
  [set g:Hom (R_n R N) (R_n R N)|is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g)].
Proof.
apply/seteqP; split=>g.
- move=>[h _ <-]; exact (orthogonal_element_orthogonal h).
- move=>hg; exists (orthogonal_element_of (@euclidean_inner_productP R N)
    (@coordinate_basisP R N) hg); first exact I.
  by apply:hom_ext=>x; rewrite orthogonal_element_ofE.
Qed.

(** Source for [orthogonal_group_hausdorff_total]: the exact
    positive finite total mass of H^nu on O(N), used
    in 3.2.48, p. 284, evaluated by 3.2.28(5),
    p. 267. The natural nu=N(N-1)/2 includes N=0. *)
Theorem orthogonal_group_hausdorff_total (R:realType) N:
  @orthogonal_group_hausdorff_measure R N (N*(N-1)%/2)%N setT=
    (stiefel_gamma_volume_scalar R (leqnn N))%:E.
Proof.
rewrite /orthogonal_group_hausdorff_measure orthogonal_group_element_full_image.
have hDegree:(N*(2*N-N-1)%/2=N*(N-1)%/2)%N by rewrite mul2n -addnn addKn.
rewrite -hDegree; exact (@euclidean_stiefel_gamma_volume R N N (leqnn N)).
Qed.

(** Source for [orthogonal_group_hausdorff_positive_finite]:
    positivity and finiteness required before every group-volume
    cancellation in 3.2.48, pp. 284, 286. *)
Corollary orthogonal_group_hausdorff_positive_finite (R:realType) N:
  (0<@orthogonal_group_hausdorff_measure R N (N*(N-1)%/2)%N setT)%E /\
  (@orthogonal_group_hausdorff_measure R N (N*(N-1)%/2)%N setT< +oo)%E.
Proof.
rewrite orthogonal_group_hausdorff_total; split; last by rewrite ltry.
by rewrite lte_fin; exact:stiefel_gamma_volume_scalar_positive.
Qed.
