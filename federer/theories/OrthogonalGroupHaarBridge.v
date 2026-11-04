(** Federer (1969), 3.2.48, p. 284: actual H^nu
    restricted to O(N) is its total mass times normalized
    Haar measure. Whole-set Hilbert isometries, positive finite
    group volume and the proved Haar uniqueness give the identification. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets functions constructive_ereal topology subtype_topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates LinearBasis HomCompositionDeterminant
  EuclideanInnerProduct InnerMetric HomInner EuclideanHomInnerCharts
  LinearGroupTopology LinearGroupSealed OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  EuclideanOrthogonalInvariantMeasures IsotropyGroupTopology TopologicalGroupUP
  InnerSpaceCountableBase CountableOpenBaseUP OpenSubspaceMeasure
  HaarIntegralUP CompactGroupHaarNormalisation TranslationInvariantHaar
  OrthogonalGroupHausdorffCarrier OrthogonalGroupHausdorffVolume OrthogonalGroupHausdorffInvariance
  MeasureUP MeasureBasic MeasureScaleIntegral StiefelGammaVolumeScalar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_group_hausdorff_haar]: the exact
    conversion from H^nu to theta_N in the last line
    of 3.2.48, p. 284. The measure equality holds
    on all group subsets. No selected Haar measure,
    extra regularity or assumed normalization is introduced. *)
Theorem orthogonal_group_hausdorff_haar (R:realType) N
    (mulS:euclidean_orthogonal_group R N->euclidean_orthogonal_group R N->euclidean_orthogonal_group R N)
    (invS:euclidean_orthogonal_group R N->euclidean_orthogonal_group R N)
    (eS:euclidean_orthogonal_group R N)
    (theta:set (euclidean_orthogonal_group R N)->\bar R):
  is_subgroup_restriction
    (linear_group_mul (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (linear_group_inv (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (linear_group_unit (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (euclidean_orthogonal_group R N) mulS invS eS ->
  is_normalised_haar_measure mulS theta ->
  @orthogonal_group_hausdorff_measure R N (N*(N-1)%/2)%N=
    measure_scale (stiefel_gamma_volume_scalar R (leqnn N)) theta.
Proof.
move=>hS hTheta.
pose V:=R_n R N.
pose HV:=Hom V V.
pose hV:=@euclidean_inner_productP R N.
pose hb:=@coordinate_basisP R N.
pose hH:=hom_inner_productP hV hV hb.
pose H:=inner_metric_space hH.
pose G:=linear_group hV hb.
pose O:=euclidean_orthogonal_group R N.
pose nu:=@orthogonal_group_hausdorff_measure R N (N*(N-1)%/2)%N.
have hGc:=orthogonal_group_lch hS.
have hCompact:=@orthogonal_group_compact_space R V _ hV N _ hb.
pose b:=@hom_rank_one_base R V V N N (@coordinate_basis R N) hb (@coordinate_basis R N).
have hB:is_basis b:=@hom_rank_one_baseP R V V N N (@coordinate_basis R N) hb
  (@coordinate_basis R N) hb.
have [U hU]:=@inner_space_countable_open_base R HV _ hH _ b hB.
have hUG:=@open_subspace_countable_open_base R H G U hU.
have hUO:=@open_subspace_countable_open_base R [the pseudoMetricType R of (set_type G)]
  (orthogonal_group hV hb) (fun i=>set_val @^-1` U i) hUG.
have hLaws:=@orthogonal_group_hausdorff_measure_laws R N (N*(N-1)%/2)%N.
have hPositive:=(@orthogonal_group_hausdorff_positive_finite R N).1.
have hFinite:=(@orthogonal_group_hausdorff_positive_finite R N).2.
have hInvariant:is_invariant_borel_measure mulS nu.
  constructor.
  - exact hLaws.1.
  - exact hLaws.2.
  - move=>K hK; apply:le_lt_trans _ hFinite.
    exact (@measure_mono R O nu hLaws.1 K setT (fun x _=>I)).
  - exact (@orthogonal_group_hausdorff_left_invariant R N mulS invS eS hS (N*(N-1)%/2)%N).
pose W:=fun _:nat=>(@setT O).
have hWo i:open (W i):=openT.
have hWc i:exists2 C:set O,compact C &W i `<=` C.
  exists setT; first exact hCompact.
  exact:subset_refl.
have hWT x:exists i,W i x by exists 0%N.
have [c hc hEqual]:=@left_haar_measure_multiple R [the pseudoMetricType R of (set_type O)]
  mulS invS eS hGc _ hUO W hWo hWc hWT nu hInvariant setT theta
  hCompact hPositive hTheta.1.
have hTotal:=hEqual setT.
rewrite hTheta.2 /nu (@orthogonal_group_hausdorff_total R N) -EFinM in hTotal.
have hScalar:(1:R)=c*stiefel_gamma_volume_scalar R (leqnn N) by case:hTotal.
have hCancel:stiefel_gamma_volume_scalar R (leqnn N)*c= 1 by rewrite mulrC -hScalar.
apply:funext=>A.
have hResult:=congr1 (fun z : \bar R =>((stiefel_gamma_volume_scalar R (leqnn N))%:E*z)%E)
  (hEqual A).
rewrite muleA -EFinM hCancel mul1e in hResult.
exact (esym hResult).
Qed.
