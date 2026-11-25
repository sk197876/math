(** Federer (1969), 3.3.18, p. 301: an actual finite
    atomic rectifiable measure refutes the converse of 3.3.17. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanInnerProduct InnerNorm InnerMetric EuclideanProjectionSpace StructureProjectionKernel
  StructureKernelOnto StructureConeUP StructureCone StructureConeBasic StructureInfiniteConeBorel
  StructureSmallConeCriterionUP StructurePlaneConeUnitDirections DenseUnitDirectionSequence
  AtomicRadialClusterMeasure AtomicRadialClusterDensity GeometricErrorBudget
  AtomicRadialClusterCarrierClosed MeasureSupportCountableCarrier MeasureSupport
  CountableSetPositiveRectifiability RectifiableSetUP MeasureUP MeasureBasic MeasureAlmostUP
  MetricDensities MeasureRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_small_cone_converse_counterexample]: the
    false-converse assertion opening Federer 3.3.18, p. 301.
    An ACTUAL finite positive atomic measure has a countable
    rectifiable carrier and every set is measurable. At its positive
    atom zero, EVERY original one-dimensional plane and aperture
    has INFINITE conical upper density. The original strict small-
    cone criterion therefore fails on a positive-mass original set,
    even though the whole original source is measure-rectifiable.
    The measure, dense unit directions and all atoms are proved
    local witnesses; no failure or infinite density is assumed. *)
Theorem structure_small_cone_converse_counterexample (R:realType):
  exists mu:set (inner_metric_space (@euclidean_inner_productP R 2))->\bar R,
    is_structure_measure mu /\(0<mu setT< +oo)%E /\
    countable (measure_support mu) /\is_measure_m_rectifiable mu 1 setT /\
    ~is_structure_small_cone_density_criterion 1 mu setT.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose zero:X:=0%R.
have [v [hUnit hDense]]:=@dense_unit_direction_sequence_exists R 2 (ltn0Sn 1).
have [mu [E [hMu [hMeas [hFinite [hCount [hZero [hOutside [hBase [hAtomic hShape]]]]]]]]]]:=
  @atomic_radial_cluster_measure_exists R 2 v.
have hStructure:is_structure_measure mu by split; last by move=>C _; exact:hMeas C.
have hCarrierClosed:=@atomic_radial_cluster_carrier_closed R 2 v E hUnit hShape.
have hSupportCountable:=measure_support_countable_closed_carrier hCount hCarrierClosed hOutside.
have hRect:is_measure_m_rectifiable mu 1 setT.
  split; last exact:hFinite.
  split; first exact:hMu.
  exists E; split; first exact:countable_set_countably_positive_rectifiable hCount.
  by rewrite /measure_almost_included setTD.
have hConical (p:euclidean_projection_space R 2 1) (s:R):(0<s<1)%R ->
    upper_metric_density 1 (measure_restrict mu
      (structure_cone (structure_projection_kernel (leqnSn 1) p) zero +oo s)) zero=+oo.
  move=>/andP[hs _].
  pose V:=structure_projection_kernel (leqnSn 1) p.
  pose U:=structure_cone V zero 2%:E s.
  have hOpen:open U:=@structure_projection_finite_cone_open R 2 1 (leqnSn 1) p zero 2%R s.
  have hMeets:=@structure_positive_plane_cone_unit_point R 2 1 (ltn0Sn 0) V s hs.
  have [j hVj]:=hDense U hOpen hMeets.
  have hInfiniteRay:structure_cone V zero +oo s (v j).
    exact:(@structure_cone_radius_mono R 2 1 V zero 2%:E +oo s (leey _) (v j) hVj).
  apply:(@atomic_radial_cluster_upper_density_infinite R 2 mu
    (structure_cone V zero +oo s) (v j) (geometric_error_budget (1:R) j) j
    hMu (hUnit j) (geometric_error_budget_positive j (@ltr01 R))).
  - move=>k hk; exact:hAtomic j k hk.
  - move=>k hk.
    have hScale:(0<(geometric_error_budget (1:R) k)^+2)%R.
      apply:exprn_gt0; exact:geometric_error_budget_positive k (@ltr01 R).
    exact:(@structure_projection_positive_ray_cone R 2 1 (leqnSn 1) p (v j) s
      ((geometric_error_budget (1:R) k)^+2)%R hScale hInfiniteRay).
have hAtZero:~structure_small_cone_density_at 1 mu setT zero.
  move=>[V [s [hs hSmall]]].
  have [p hKernel]:=@structure_projection_kernel_onto R 2 1 (leqnSn 1) V.
  rewrite setTI -hKernel (hConical p s hs) in hSmall.
  by have:=lt_le_trans hSmall (leey _); rewrite ltxx.
have hFailure:~is_structure_small_cone_density_criterion 1 mu setT.
  move=>hNull.
  have hSub:[set zero] `<=` setT `\` [set a|structure_small_cone_density_at 1 mu setT a].
    by move=>x ->; split.
  have hBound:=measure_mono hMu hSub.
  rewrite hNull in hBound.
  have hFalse:=le_trans hBase hBound; by rewrite lee_fin ler10 in hFalse.
have hPositive:(0<mu setT)%E.
  have hBound:=measure_mono hMu (subsetT [set zero]).
  have hOne:1<=mu setT:=le_trans hBase hBound.
  have hZeroOne:(0<(1 : \bar R))%E by rewrite lte_fin ltr01.
  exact:lt_le_trans hZeroOne hOne.
exists mu; split; first exact:hStructure.
split; first by apply/andP; split.
split; first exact:hSupportCountable.
by split.
Qed.
