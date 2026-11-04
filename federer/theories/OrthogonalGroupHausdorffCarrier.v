(** Federer (1969), 3.2.48, p. 284: Hausdorff measure
    on O(N) in its actual relative carrier and Hilbert
    Hom metric. The carrier inclusions are the same two
    inclusions used by the existing normalized Haar measure. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets functions constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric HomInner EuclideanHomInnerCharts LinearGroupTopology OrthogonalGroupTopology
  EuclideanOrthogonalInvariantMeasures OrthogonalGroupHaarMeasure HausdorffMeasure
  HausdorffClosedCoverAgreement MeasureUP BorelRegularMeasureUP
  OpenSubspaceMeasure SubspaceBorelRegularMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_group_hausdorff_measure]: H^q
    regarded as a measure on the actual group O(N),
    as in 3.2.48, p. 284. This is the image-set
    restriction of the original ambient Hausdorff measure,
    with no replacement metric or selected retraction. *)
Definition orthogonal_group_hausdorff_measure (R:realType) N q
    (A:set (euclidean_orthogonal_group R N)):=
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R N N)) q
    (@orthogonal_element_map R (R_n R N) (@euclidean_inner_product R N)
      (@euclidean_inner_productP R N) N (@coordinate_basis R N) (@coordinate_basisP R N) @` A).

(** Source for [orthogonal_group_hausdorff_measure_laws]: the
    actual relative-carrier Hausdorff restriction is a Borel
    regular measure, by 2.2.3, p. 61, supporting
    the Haar identification in 3.2.48, p. 284. *)
Theorem orthogonal_group_hausdorff_measure_laws (R:realType) N q:
  is_measure (@orthogonal_group_hausdorff_measure R N q) /\
  is_borel_regular_measure (@orthogonal_group_hausdorff_measure R N q).
Proof.
pose hV:=@euclidean_inner_productP R N.
pose hb:=@coordinate_basisP R N.
pose H:=inner_metric_space (hom_inner_productP hV hV hb).
pose G:=linear_group hV hb.
pose O:=orthogonal_group hV hb.
pose rho:=@hausdorff_measure R H q.
pose mu:=open_subspace_measure (S:=G) rho.
pose nu:=open_subspace_measure (S:=O) mu.
have hRho:=@hausdorff_measure_is_measure R H q.
have hMu:=@subspace_image_measure_laws R H G rho hRho.
have hNu:=@subspace_image_measure_laws R [the topologicalType of (set_type G)] O mu hMu.
have hMuReg:=@subspace_borel_regular_measure R H G rho hRho
  (@hausdorff_measure_borel_regular R H q).
have hNuReg:=@subspace_borel_regular_measure R [the topologicalType of (set_type G)] O mu hMu hMuReg.
have hProof:@euclidean_hom_inner_productP R N N=hom_inner_productP hV hV hb.
  exact:Prop_irrelevance.
have hEqual:@orthogonal_group_hausdorff_measure R N q=nu.
  rewrite /orthogonal_group_hausdorff_measure hProof; apply:funext=>A.
  rewrite /nu /mu /open_subspace_measure.
  congr (@hausdorff_measure R H q); apply/seteqP; split=>x.
  - move=>[a ha <-]; exists (set_val a); last reflexivity.
    by exists a.
  - move=>[a [g hg <-] <-]; exists g; last reflexivity.
    exact hg.
by rewrite hEqual; split.
Qed.
