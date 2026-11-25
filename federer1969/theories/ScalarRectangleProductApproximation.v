(** Federer (1969), 4.1.23, p. 380:
    the original scalar rectangle times a
    compact transverse Lebesgue zero-current has
    an equal-mass real polyhedral approximant
    with arbitrarily small flat error in
    the exact compact Cartesian box. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology ring.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm InnerConvex HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanBlockCoordinates EuclideanCartesianMap
  EuclideanCartesianConvexGeometry CurrentSpaces CurrentCharacteristicDensity
  CurrentDiracDensity CurrentMassSealed CurrentFlatNorm NormalCurrentsUP SmoothCompactSet TopologicalBorel
  CurrentCartesianDomain CurrentCartesianCompact CurrentCartesianProductSealed
  CurrentAmbientCartesianProduct CurrentDomainTransport CurrentDegreeTransport
  CurrentMassDegreeTransport CurrentEqualDomainQuantities CurrentEqualDomainFlat
  CurrentCartesianAtomicReplacement CompactCharacteristicCurrent
  OrientedRectangleDomain ScalarSegmentFactors CurrentScalarRectangle
  CurrentScalarRectangleVertex ScalarRectangleBoxDensity
  ClosedCoordinateBoxConvex ClosedCoordinateBoxGeometry
  ScalarRectangleAtomicPolyhedral PositiveAtomicZeroCurrentMass TransverseAtomicApproximation
  FiniteTaggedBorelPartitionUP
  PolyhedralCurrentAlgebra EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  MeasureUP MeasureBasic.
From Federer Require Import ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectangleProductApproximation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable f : seq (R*R).
Hypothesis hOrdered : @scalar_rectangle_ordered R f.
Local Notation m := (oriented_rectangle_dimension (@scalar_segment_factors R f)).
Variable n : nat.
Local Notation Full := (fun d : nat => fun _ : R_n R d => True).
Local Notation hFull := (fun (d : nat) (x : R_n R d) (_ : True) =>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Local Notation lower := ([ffun i : 'I_m => (nth (0,0) f (val i)).1] : R_n R m).
Local Notation upper := ([ffun i : 'I_m => (nth (0,0) f (val i)).2] : R_n R m).
Local Notation D := (@closed_coordinate_box_index R m lower upper).
Variable B : smooth_compact_set hNY (Full n).
Hypothesis hBConvex : is_inner_convex (smooth_compact_carrier B).
Local Notation Box := (@euclidean_cartesian_set R m n (smooth_compact_carrier D)
  (smooth_compact_carrier B)).
Local Notation hBox := (@current_cartesian_compact R m n (smooth_compact_carrier D)
  (smooth_compact_carrier B) (smooth_compact_is_compact D) (smooth_compact_is_compact B)).
Local Notation K := (@Build_smooth_compact_set R (R_n R (m+n))
  (inner_norm (@euclidean_inner_productP R (m+n))) hNZ (Full (m+n)) Box
  (fun _ _ => Logic.I) hBox).
Local Notation AB := (@euclidean_cartesian_set R m n (Full m) (Full n)).
Local Notation hAB := (@current_cartesian_domain_open R m n (Full m) (Full n)
  (hFull m) (hFull n)).
Local Notation KAB := (@Build_smooth_compact_set R (R_n R (m+n))
  (inner_norm (@euclidean_inner_productP R (m+n))) hNZ AB Box
  (fun _ _ => conj Logic.I Logic.I) hBox).
Local Notation TrD := (@current_domain_transport R h2 (m+n) AB hAB (Full (m+n))
  (@current_cartesian_full_domain R m n) (hFull (m+n)) (m+0)).
Local Notation TrG := (@current_degree_transport R h2 (m+n) (Full (m+n)) (hFull (m+n))
  (m+0) m (addn0 m)).
Local Notation Rectangle := (@current_scalar_rectangle R h2 f).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation hLeb := (euclidean_lebesgue_is_measure R n).
Local Notation hBM := (@euclidean_distribution_measure_borel R n (smooth_compact_carrier B)
  (closed_borel_set (compact_closed (@metric_hausdorff R (real_norm_metric_space hNY))
    (smooth_compact_is_compact B)))).
Local Notation S := (@current_characteristic_density R h2 n 0%N Leb hLeb
  (@euclidean_distribution_measure_borel R n) (@euclidean_distribution_measure_compact_finite R n)
  (smooth_compact_carrier B) hBM (@current_scalar_multivector_unit R n)).
Local Notation Raw := (@CartesianCurrentProduct.value R h2 m n m 0%N
  (Full m) (Full n) (hFull m) (hFull n)).
Local Notation Product := (@current_ambient_cartesian_product R h2 m n m 0%N).
Local Notation T := (TrG (Product Rectangle S)).
Local Notation C := (@current_space R h2 (m+n) (Full (m+n)) (hFull (m+n)) m).
Local Notation F := (@current_flat_norm R h2 (m+n) m (Full (m+n)) (hFull (m+n)) K).
Local Notation M := (@CurrentMass.value R h2 (m+n) m (Full (m+n)) (hFull (m+n))).

(** Source for [scalar_rectangle_product_polyhedral_approximation]:
    P=R times Q satisfies F_A(T-P)<=epsilon,
    M(P)=M(T), and P belongs to
    the original real polyhedral class
    in the same compact box A,
    Federer 4.1.23, p. 380.
    The m=0 rectangle and empty,
    null or R^0 transverse factor remain allowed. *)
Theorem scalar_rectangle_product_polyhedral_approximation epsilon (hEpsilon : 0<epsilon) :
  exists P : C,
    @polyhedral_current_subspace R h2 (m+n) m (Full (m+n)) (hFull (m+n)) K P /\
    (F (T-P)<=epsilon%:E)%E /\ M P=M T.
Proof.
have [_ [hRectangle [_ [normalMass [hNormalPositive hNormalMass]]]]] :=
  @scalar_rectangle_box_density_properties R h2 f hOrdered.
have hVolumeFinite := @euclidean_distribution_measure_compact_finite R n
  (smooth_compact_carrier B) (smooth_compact_is_compact B).
have hVolumeNumber : Leb (smooth_compact_carrier B) \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative hLeb (smooth_compact_carrier B))).
pose b := fine (Leb (smooth_compact_carrier B)).
have hB : 0<=b := fine_ge0 (measure_nonnegative hLeb (smooth_compact_carrier B)).
have hVolume : Leb (smooth_compact_carrier B)=b%:E by symmetry; exact: fineK hVolumeNumber.
have hBOne : 0<b+1.
  apply: (lt_le_trans (@ltr01 R)); by rewrite lerDr.
have hDenominator : 0<normalMass*(b+1) := mulr_gt0 hNormalPositive hBOne.
pose d := epsilon/(normalMass*(b+1)).
have hD : 0<d := divr_gt0 hEpsilon hDenominator.
have [I [A [tag [hPartition [hTags [_ [hQMass hQError]]]]]]] :=
  @transverse_atomic_flat_mass_approximation_exists R h2 n B hBConvex d hD.
pose weights := fun i : I => fine (Leb (A i)).
pose Q := @positive_atomic_zero_current R h2 n I tag weights.
have hMassS : @CurrentMass.value R h2 n 0%N (Full n) (hFull n) S=b%:E.
  rewrite -hVolume.
  exact: (@compact_characteristic_zero_current_properties R h2 n
    (smooth_compact_carrier B) hBM B (fun _ hx => hx)).2.1.
have hMassQ : @CurrentMass.value R h2 n 0%N (Full n) (hFull n) Q=b%:E.
  exact: eq_trans hQMass hMassS.
have hReplacement := @current_cartesian_atomic_replacement R h2 m n m
  (Full m) (Full n) (hFull m) (hFull n) D B KAB (erefl Box)
  Rectangle S Q hRectangle.1 hRectangle.2 normalMass b (d*b)
  hNormalMass hMassS hMassQ hQError.
pose P : C := TrG (Product Rectangle Q).
have hFlatTransport Z :
    F (TrG (TrD Z))=@current_flat_norm R h2 (m+n) (m+0) AB hAB KAB Z.
  rewrite current_equal_degree_flat_norm.
  exact: (@current_equal_domain_flat_norm R h2 (m+n) (m+0) AB (Full (m+n))
    hAB (hFull (m+n)) (@current_cartesian_full_domain R m n) KAB K (erefl Box) Z).
have hMassTransport Z : M (TrG (TrD Z))=
    @CurrentMass.value R h2 (m+n) (m+0) AB hAB Z.
  rewrite current_mass_degree_transport; exact: current_equal_domain_mass.
have hDifference : TrG (TrD (Raw Rectangle S-Raw Rectangle Q))=T-P.
  by rewrite (linB (hom_linear TrD)) (linB (hom_linear TrG)).
have hError : (F (T-P)<=(normalMass*(d*b))%:E)%E.
  rewrite -hDifference hFlatTransport; exact: hReplacement.1.
have hCost : normalMass*(d*b)<=epsilon.
  have hEnlarge : d*b<=d*(b+1).
    apply: (@ler_wpM2l R d (ltW hD) b (b+1)); by rewrite lerDl.
  apply: (le_trans (@ler_wpM2l R normalMass (ltW hNormalPositive) (d*b) (d*(b+1)) hEnlarge)).
  have hEndpoint : (normalMass*(b+1))*d=epsilon.
    by rewrite /d mulrC divfK ?gt_eqF.
  have hCommutation : normalMass*(d*(b+1))=(normalMass*(b+1))*d by ring.
  by rewrite hCommutation hEndpoint.
have hBoxConvex : is_inner_convex Box := euclidean_cartesian_convex
  (@closed_coordinate_box_convex R m lower upper) hBConvex.
have hCorners i x (hx : @is_current_scalar_rectangle_vertex R f x) :
    smooth_compact_carrier K (@euclidean_block_join R m n (x,tag i)).
  change (smooth_compact_carrier D (euclidean_block_split (euclidean_block_join (x,tag i))).1 /\
    smooth_compact_carrier B (euclidean_block_split (euclidean_block_join (x,tag i))).2).
  rewrite euclidean_block_joinK; split.
  - exact: (@scalar_rectangle_corners_in_closed_box R f hOrdered x hx).
  - exact: (@finite_tagged_partition_inside R (real_norm_metric_space hNY)
      (smooth_compact_carrier B) (d/2) I A tag hPartition i (tag i) (hTags i)).
have hPolyhedral : @polyhedral_current_subspace R h2 (m+n) m
    (Full (m+n)) (hFull (m+n)) K P.
  exact: (@scalar_rectangle_atomic_product_polyhedral R h2 f n K hBoxConvex I tag weights hCorners).
exists P; split; first exact: hPolyhedral.
split.
- apply: (le_trans hError); by rewrite lee_fin.
- rewrite /P /current_ambient_cartesian_product !hMassTransport.
  exact: hReplacement.2.
Qed.
End RectangleProductApproximation.
