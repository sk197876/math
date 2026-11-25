(** Federer (1969), 3.2.48, pp. 284, 286: normalized Haar measure
    on the actual orthogonal group is Borel regular. The already proved
    Hausdorff identification supplies its all-set regularity and the
    original subgroup topology has a countable open base. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets functions constructive_ereal topology subtype_topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates CoordinateProjection LinearBasis
  HomCompositionDeterminant EuclideanInnerProduct InnerMetric HomInner HomSpaceTopology EuclideanHomInnerCharts
  LinearGroupTopology LinearGroupSealed OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  EuclideanOrthogonalInvariantMeasures IsotropyGroupTopology TopologicalGroupUP
  InnerSpaceCountableBase CountableOpenBaseUP OpenSubspaceMeasure
  HaarIntegralUP CompactGroupHaarNormalisation OrthogonalGroupHausdorffCarrier OrthogonalGroupHaarBridge
  BorelRegularMeasureUP MeasureUP MeasureScaleIntegral MeasureScaleBorelRegular StiefelGammaVolumeScalar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_normalised_haar_borel_regular]: the actual
    normalized Haar measure used in 3.2.48, p. 286, has true Borel
    hulls on every subset. This follows from the positive finite
    Hausdorff normalization, rather than an extra regularity premise. *)
Theorem orthogonal_normalised_haar_borel_regular (R:realType) N
    (mulS:euclidean_orthogonal_group R N->euclidean_orthogonal_group R N->euclidean_orthogonal_group R N)
    (invS:euclidean_orthogonal_group R N->euclidean_orthogonal_group R N)
    (eS:euclidean_orthogonal_group R N) (theta:set (euclidean_orthogonal_group R N)->\bar R):
  is_subgroup_restriction
    (linear_group_mul (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (linear_group_inv (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (linear_group_unit (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (euclidean_orthogonal_group R N) mulS invS eS ->
  is_normalised_haar_measure mulS theta ->is_borel_regular_measure theta.
Proof.
move=>hGroup hTheta.
have [hMu hReg]:=@orthogonal_group_hausdorff_measure_laws R N (N*(N-1)%/2)%N.
have hBridge:=orthogonal_group_hausdorff_haar hGroup hTheta.
have hPositive:=stiefel_gamma_volume_scalar_positive R (leqnn N).
have hInverse:=measure_scale_inverse theta hPositive.
rewrite -hBridge in hInverse.
rewrite -hInverse.
apply:(measure_scale_borel_regular hMu _ hReg).
by rewrite invr_gt0.
Qed.

(** Source for [orthogonal_group_countable_open_base]: the actual
    subgroup topology has a countable open base, supporting the
    completed measurable product average in 3.2.48, p. 286.
    Restrict the original finite-dimensional Hilbert Hom base twice. *)
Theorem orthogonal_group_countable_open_base (R:realType) N:
  exists U:nat->set (euclidean_orthogonal_group R N),is_countable_open_base U.
Proof.
pose V:=R_n R N.
pose hV:=@euclidean_inner_productP R N.
pose hb:=@coordinate_basisP R N.
pose hH:=hom_inner_productP hV hV hb.
pose H:=inner_metric_space hH.
pose G:=linear_group hV hb.
pose O:=orthogonal_group hV hb.
pose b:=@hom_rank_one_base R V V N N (@coordinate_basis R N) hb (@coordinate_basis R N).
have hB:=@hom_rank_one_baseP R V V N N (@coordinate_basis R N) hb (@coordinate_basis R N) hb.
have [U hU]:=@inner_space_countable_open_base R (Hom V V) _ hH _ b hB.
have hUG:=@open_subspace_countable_open_base R H G U hU.
have hUO:=@open_subspace_countable_open_base R [the pseudoMetricType R of (set_type G)] O
  (fun i=>set_val @^-1` U i) hUG.
exists (fun i=>set_val @^-1` (set_val @^-1` U i)); exact hUO.
Qed.
