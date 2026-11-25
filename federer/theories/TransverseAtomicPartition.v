(** Federer (1969), 4.1.23, p. 380:
    the transverse finite Borel partition gives
    the literal positive atomic chain Q,
    exact preservation of mass, and the
    displayed sum of flat errors bounded
    by diameter(B_k) times Lebesgue(B_k). *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm InnerConvex HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingPairing
  CurrentSpaces CurrentDirac CurrentDiracDensity CurrentSupportGeometry
  TopologicalBorel
  CurrentCharacteristicDensity CurrentDensityAction CurrentDensityArithmetic
  CurrentDensityUniqueness CurrentMassSealed CurrentCompactSmoothValue
  NormalCurrentsUP SmoothCompactSet CurrentFlatNorm CurrentFlatFiniteSumBound
  CompactCharacteristicCurrent NormalZeroCurrentAtomicFlatBound
  PositiveAtomicZeroCurrentMass FiniteTaggedBorelPartitionUP
  FiniteTaggedPartitionCharacteristic MetricDiameterUP MetricDiameter
  MetricDiameterClosure EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  MeasureUP MeasureBasic CharacteristicFunctionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section TransversePartition.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation hLeb := (euclidean_lebesgue_is_measure R n).
Local Notation unit := (@current_scalar_multivector_unit R n).
Local Notation C := (@current_space R h2 n Full hFull 0%N).
Local Notation M := (@CurrentMass.value R h2 n 0%N Full hFull).
Variable B : smooth_compact_set hNX Full.
Hypothesis hConvex : is_inner_convex (smooth_compact_carrier B).
Local Notation FB := (@current_flat_norm R h2 n 0%N Full hFull B).
Local Notation carrier := (smooth_compact_carrier B : set XT).
Local Notation hBMeas := (@euclidean_distribution_measure_borel R n carrier
  (closed_borel_set (compact_closed (@metric_hausdorff R XT) (smooth_compact_is_compact B)))).
Local Notation S := (@current_characteristic_density R h2 n 0%N Leb hLeb
  (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) carrier hBMeas unit).
Variables (I : finType) (A : I -> set X) (tag : I -> X) (e d : R).
Hypothesis hP : is_finite_tagged_borel_partition carrier e A tag.
Hypothesis hTags : forall i, A i (tag i).
Hypothesis hD : forall i, (@extended_metric_diameter R XT (A i)<=d%:E)%E.
Local Notation hCells := (fun i => @euclidean_distribution_measure_borel R n (A i)
  (@finite_tagged_partition_borel R XT carrier e I A tag hP i)).
Local Notation piece := (fun i => @current_characteristic_density R h2 n 0%N Leb hLeb
  (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) (A i) (hCells i) unit).
Local Notation weight := (fun i => fine (Leb (A i))).
Local Notation diameter := (fun i => fine (@extended_metric_diameter R XT (A i))).
Local Notation Q := (@positive_atomic_zero_current R h2 n I tag weight).

(** Source for [transverse_partition_atomic_estimate]:
    S=sum_k S_k, M(Q)=M(S), and
    F_B(S-Q)<=sum_k diam(B_k) M(S_k)
    <=d M(S), the literal finite
    partition estimates of Federer 4.1.23,
    p. 380. The original S_k
    are actual Lebesgue characteristic zero-currents. *)
Theorem transverse_partition_atomic_estimate :
  S=\sum_i piece i /\ M Q=M S /\
    (FB (S-Q)<=(\sum_i diameter i*weight i)%:E)%E /\
    (\sum_i diameter i*weight i<=d*fine (Leb carrier)).
Proof.
have hBFinite := @euclidean_distribution_measure_compact_finite R n carrier
  (smooth_compact_is_compact B).
have hInside i : A i `<=` carrier := @finite_tagged_partition_inside R XT carrier e I A tag hP i.
have hNumbers i : Leb (A i) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hLeb (A i))).
  exact: le_lt_trans (measure_mono hLeb (@hInside i)) hBFinite.
have hWeights i : 0<=weight i := fine_ge0 (measure_nonnegative hLeb (A i)).
have hDiameterNumbers i : @extended_metric_diameter R XT (A i) \is a fin_num.
  rewrite (ge0_fin_numE (metric_diameter_nonnegative
    (@extended_metric_diameter_specification R XT (A i)))).
  exact: le_lt_trans (hD i) (ltry d).
have hDiameterValue i : @extended_metric_diameter R XT (A i)=(diameter i)%:E.
  symmetry; exact: fineK (hDiameterNumbers i).
have hDiameterNonnegative i : 0<=diameter i.
  exact: fine_ge0 (metric_diameter_nonnegative
    (@extended_metric_diameter_specification R XT (A i))).
have hDiameterBound i : diameter i<=d.
  have h := hD i; by rewrite hDiameterValue lee_fin in h.
have hPieces i : @normal_currents_supported_in R h2 n Full hFull 0%N B (piece i) /\
    M (piece i)=Leb (A i) /\ forall hCompact,
      @current_compact_total R h2 n Full hFull (piece i) hCompact=weight i.
  exact: (@compact_characteristic_zero_current_properties R h2 n (A i) (hCells i)
    B (@hInside i)).
have hSum : S=\sum_i piece i.
  have hSumAction := @current_density_finite_sum_action R h2 n 0%N Leb hLeb I
    (fun i x => @CharacteristicFunction.value R X (A i) x*:unit) piece
    (fun i => @current_characteristic_density_action R h2 n 0%N Leb hLeb
      (@euclidean_distribution_measure_borel R n)
      (@euclidean_distribution_measure_compact_finite R n) (A i) (hCells i) unit).
  have hFunction : (fun x => \sum_i @CharacteristicFunction.value R X (A i) x*:unit)=
      (fun x => @CharacteristicFunction.value R X carrier x*:unit).
    apply: funext=> x; rewrite -scaler_suml.
    by rewrite -(@finite_tagged_partition_characteristic_sum R XT carrier e I A tag hP x).
  rewrite hFunction in hSumAction.
  apply: (@current_density_action_unique R h2 n 0%N Leb
    (fun x => @CharacteristicFunction.value R X carrier x*:unit)).
  - exact: (@current_characteristic_density_action R h2 n 0%N Leb hLeb
      (@euclidean_distribution_measure_borel R n)
      (@euclidean_distribution_measure_compact_finite R n) carrier hBMeas unit).
  - exact: hSumAction.
have hMassS := (@compact_characteristic_zero_current_properties R h2 n carrier hBMeas
  B (fun _ hx => hx)).2.1.
have hMassQ := (@positive_atomic_zero_current_mass R h2 n B I tag weight
  (fun i => @hInside i (tag i) (hTags i)) hWeights).1.
have hWeightSum := @finite_tagged_partition_measure_sum R XT Leb hLeb carrier e I A tag
  hP hBMeas hBFinite hCells.
have hMass : M Q=M S by rewrite hMassQ hMassS hWeightSum.
have hEach i : (FB (piece i-weight i*:@dirac_current R h2 n Full hFull (tag i))<=
    (diameter i*weight i)%:E)%E.
  have hClosedB : closed (carrier:set XT) := compact_closed
    (@metric_hausdorff R XT) (smooth_compact_is_compact B).
  have hClosureInside : @closure XT (A i) `<=` carrier.
    move=> x hx; apply: hClosedB.
    exact: (@closureS XT (A i) carrier (@hInside i) x hx).
  have hClosureCompact : @compact XT (@closure XT (A i)).
    exact: (@subclosed_compact XT (@closure XT (A i)) carrier
      (@closed_closure XT (A i)) (smooth_compact_is_compact B) hClosureInside).
  pose K := @Build_smooth_compact_set R X NX hNX Full (@closure XT (A i))
    (fun _ _ => Logic.I) hClosureCompact.
  have hCellProperties := @compact_characteristic_zero_current_properties R h2 n (A i)
    (hCells i) K (@subset_closure XT (A i)).
  have hDistance x : @current_support R h2 n Full hFull 0%N (piece i) x ->
      NX (x-tag i)<=diameter i.
    move=> hx.
    have hPairs y z (hy : A i y) (hz : A i z) : @mdist R XT y z<=diameter i.
      have h := @metric_diameter_upper R XT (A i) _
        (@extended_metric_diameter_specification R XT (A i)) y z hy hz.
      by rewrite hDiameterValue lee_fin in h.
    exact: (@metric_pair_bound_closure R XT (A i) (diameter i) hPairs x (tag i)
      (hCellProperties.1.2 x hx) (@subset_closure XT (A i) (tag i) (hTags i))).
  have hBound := @normal_zero_current_atomic_flat_bound R h2 n B hConvex
    (tag i) (@hInside i (tag i) (hTags i)) (piece i) (hPieces i).1.1
    (diameter i) (hDiameterNonnegative i) (hPieces i).1.2 hDistance.
  cbn zeta in hBound.
  rewrite ((hPieces i).2.2 (hPieces i).1.1.2) (hPieces i).2.1
    -(fineK (hNumbers i)) -EFinM in hBound.
  exact: hBound.
have hSumBound := @current_flat_norm_finite_sum_bound R h2 n 0%N Full hFull B I
  (fun i => piece i-weight i*:@dirac_current R h2 n Full hFull (tag i))
  (fun i => diameter i*weight i) hEach.
have hDifference : S-Q=\sum_i (piece i-weight i*:@dirac_current R h2 n Full hFull (tag i)).
  by rewrite sumrB -hSum /positive_atomic_zero_current.
have hRealWeightSum : \sum_i weight i=fine (Leb carrier).
  by rewrite -hWeightSum.
split; first exact: hSum.
split; first exact: hMass.
split; first by rewrite hDifference.
rewrite -hRealWeightSum mulr_sumr; apply: ler_sum=> i _.
exact: (@ler_wpM2r R (weight i) (hWeights i) (diameter i) d (hDiameterBound i)).
Qed.
End TransversePartition.
