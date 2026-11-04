(** Federer (1969), 3.2.46, p. 282: the
    unweighted coarea theorem holds for the actual
    Riemannian metrics. Proved local distortions, original
    fibre measurability and countable Borel partitions
    give the global identity by a geometric squeeze. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff
  RiemannianPathLipschitz RiemannianChartReference RiemannianJacobianDensityMeasure
  RiemannianMapJacobian RiemannianCoareaFibreMeasurable RiemannianLocalCoareaComparison
  RiemannianCoareaSourceDensityIntegral MeasureLocalFibreIntegralComparison
  MappingMultiplicity PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP
  MeasureSubsetIntegral MeasureNonnegativeIntegral BorelRegularMeasureUP TopologicalBorel
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_coarea_formula]: the genuine
    unweighted coarea identity of 3.2.11, p. 249,
    for the actual Riemannian metrics asserted by
    3.2.46, p. 282. Exactly n<m, original
    path-Lipschitz continuity and completed source-volume
    measurability are assumed. Original non-Borel sources,
    singular maps, empty charts, zero target dimension
    and infinite integral values are retained. *)
Theorem riemannian_coarea_formula (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hpSource : 0<=m%:R :> R) (hpTarget : 0<=n%:R :> R)
    (hpFibre : 0<=(m-n)%:R :> R) (S : set (riemannian_metric_space hg)) :
  (n<m)%N -> is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hpSource) S ->
  is_measure_integral (riemannian_hausdorff_measure hh n%:R hpTarget)
    (partial_function_total (fun y=>(riemannian_hausdorff_measure hg (m-n)%:R hpFibre
      (mapping_fibre f S y) : extended_real_line R)))
    (riemannian_jacobian_measure f hpSource n S).
Proof.
move=> hnm hLip hS.
pose X := [the topologicalType of riemannian_metric_space hg].
pose Y := [the choiceType of riemannian_metric_space hh].
pose mu := riemannian_hausdorff_measure hg m%:R hpSource.
pose nu := riemannian_jacobian_measure f hpSource n.
pose sigma := riemannian_hausdorff_measure hg (m-n)%:R hpFibre.
pose beta := riemannian_hausdorff_measure hh n%:R hpTarget.
pose p := fun y : Y=>(sigma (mapping_fibre f S y) : extended_real_line R).
have hMu := @riemannian_hausdorff_is_measure R m A g hg m%:R hpSource.
have hNu := @riemannian_jacobian_measure_is_measure R m n A B g h hg hh f hpSource n hLip.
have hSigma := @riemannian_hausdorff_is_measure R m A g hg (m-n)%:R hpFibre.
have hBeta := @riemannian_hausdorff_is_measure R n B h hh n%:R hpTarget.
have [U hBase] := @riemannian_chart_countable_open_base R m A g hg.
have hBorel C (hC : @borel_set X C) : measure_measurable mu C /\
    measure_measurable nu C /\ measure_measurable sigma C.
  have hCMu := @borel_regular_borel_measurable R X mu hMu
    (@riemannian_hausdorff_borel_regular R m A g hg m%:R hpSource) C hC.
  split; first exact hCMu; split.
  - exact:(@riemannian_jacobian_measure_measurable R m n A B g h hg hh f hpSource n C hLip hCMu).
  - exact:(@borel_regular_borel_measurable R X sigma hSigma
      (@riemannian_hausdorff_borel_regular R m A g hg (m-n)%:R hpFibre) C hC).
have hMeas := @riemannian_coarea_fibre_mass_measurable R m n A B g h hg hh f
  hpSource hpTarget hpFibre S (ltnW hnm) hLip hS.
have hPositive : measure_almost_everywhere beta (partial_extended_nonnegative_locus (partial_function_total p)).
  apply:(@measure_almost_everywhere_mono R Y beta hBeta classical_sets.setT _ _
    (measure_almost_everywhere_true hBeta))=> y _.
  exists (p y); split; first by []; exact (@measure_nonnegative R X sigma hSigma (mapping_fibre f S y)).
have [hIntegral ha] := @nonnegative_measurable_function_integral R Y beta hBeta
  (partial_function_total p) hMeas hPositive.
have hValue := @measure_local_fibre_geometric_identity R X Y mu nu sigma beta f U
  ((n+n).+1+(m-n)+1) hMu hNu hSigma hBeta hBase hBorel
  (@riemannian_local_coarea_comparison R m n A B g h hg hh f
    hpSource hpTarget hpFibre hnm hLip) S _ hS hIntegral.
rewrite hValue in hIntegral; exact hIntegral.
Qed.

(** Source for [federer_3_2_46_coarea_sets]: both genuine
    subset and whole-fibre integral graphs in the
    unweighted coarea assertion of 3.2.46, p. 282,
    extending 3.2.11, pp. 248–249. The
    actual original Jacobian and metrics are retained;
    no chosen differential, Borelness, finite mass,
    rank or independent fibre-integrability premise is added. *)
Theorem federer_3_2_46_coarea_sets (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hpSource : 0<=m%:R :> R) (hpTarget : 0<=n%:R :> R)
    (hpFibre : 0<=(m-n)%:R :> R) (S : set (riemannian_metric_space hg)) :
  (n<m)%N -> is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hpSource) S ->
  exists a, is_measure_subset_integral (riemannian_hausdorff_measure hg m%:R hpSource) S
    (extended_riemannian_map_jacobian f n) a /\
    is_measure_integral (riemannian_hausdorff_measure hh n%:R hpTarget)
      (partial_function_total (fun y=>(riemannian_hausdorff_measure hg (m-n)%:R hpFibre
        (mapping_fibre f S y) : extended_real_line R))) a.
Proof.
move=> hnm hLip hS; exists (riemannian_jacobian_measure f hpSource n S); split.
- exact:(@riemannian_coarea_jacobian_measure_integral R m n A B g h hg hh f hpSource S hLip hS).
- exact:(@riemannian_coarea_formula R m n A B g h hg hh f hpSource hpTarget hpFibre S hnm hLip hS).
Qed.
