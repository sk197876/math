(** Finite-cutoff upper integral for the original Gillespie
    section inequality in Federer (1969), 3.2.45, p. 280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanLebesgueDimensions ProjectionMeasureUP IntegralGeometricGauge IntegralGeometricMeasure IntegralGeometricClosedCovers
  ConvexSectionCutoffGenerator MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleCutoffCost
  MetricScaleApproximation CaratheodoryLimitUP NonnegativeSum BorelClosedProjection TopologicalBorel SuslinSetUP
  MeasureUP MeasureAlmostUP MeasureBasic MeasureIndexedCover ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureUpperIntegralMonotone MeasureAlmostBasic TotalCountableNonnegativeIntegral ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_geometric_section_cutoff_integral_bound]: supporting
    closed-convex covering deduction on p. 280 of
    Federer 3.2.45. Keep a fixed positive section
    cutoff. A source cover at that same finite
    cutoff has compact convex generators. Their original
    intrinsic section functions are nonnegative integrable
    majorants, with integral at most the source costs.
    Countable integration, 2.4.8, p. 84, and the
    source covering infimum give the upper-integral
    estimate. No source or section measurability is
    assumed. Repeated sections retain their original
    source indices; either empty block is retained. *)
Theorem convex_geometric_section_cutoff_integral_bound (R : realType) m q k (hKQ : (k<=q)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R (m+q)))) (d M : R)
    (nu : set (inner_metric_space (@euclidean_inner_productP R q)) -> \bar R) :
  (0<d)%R ->
  is_metric_scale_envelope
    (fun j : closed_convex_euclidean_sets R q => val j)
    (fun j => @integral_geometric_gauge R q k hKQ 1 (val j)) d%:E nu ->
  @convex_integral_geometric_measure R (m+q) (m+k) (leq_add (leqnn m) hKQ) 1 A<=M%:E ->
  measure_upper_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y : inner_metric_space (@euclidean_inner_productP R m) =>
      (nu [set z | A (@euclidean_block_join R m q (y,z))] : extended_real_line R)))<=M%:E.
Proof.
move=> hd hNu hMass.
apply: (@extended_upper_bound_from_scaled_errors R _ M 1%R ler01)=> eps hEps.
rewrite mul1r.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R q).
pose Z := inner_metric_space (@euclidean_inner_productP R (m+q)).
pose J := closed_convex_euclidean_sets R (m+q).
pose S := fun j : J => val j.
pose c := fun j : J => @integral_geometric_gauge R (m+q) (m+k) (leq_add (leqnn m) hKQ) 1 (S j).
pose xi := @metric_scale_envelope R Z J S c d%:E.
have hXi := @metric_scale_envelope_specification R Z J S c d%:E.
have hSource := @convex_integral_geometric_closed_cover_specification R (m+q) (m+k)
  (leq_add (leqnn m) hKQ) 1 (lexx 1).
have hDE : (0<d%:E)%E by rewrite lte_fin.
have hNear : xi A<(M+eps)%R%:E.
  apply: le_lt_trans (@caratheodory_limit_upper R Z J S c _ hSource A d%:E xi hDE hXi) _.
  apply: le_lt_trans hMass _; rewrite lte_fin ltrDl; exact hEps.
have [G [hG [hDiameter [hCover hCost]]]] := metric_scale_envelope_approximation hXi hNear.
pose rho := fun (j : J) (y : X) =>
  (@integral_geometric_gauge R q k hKQ 1 [set z | S j (@euclidean_block_join R m q (y,z))] : extended_real_line R).
have hMajor j : exists a : R, G j ->
    (forall y, 0<=rho j y) /\
    is_measure_integral (@euclidean_lebesgue_measure R m) (partial_function_total (rho j)) a%:E /\
    a%:E<=c j /\
    forall y, nu [set z | S j (@euclidean_block_join R m q (y,z))]<=rho j y.
  case: (pselect (G j))=> hj.
  - have [a hA] := @convex_section_cutoff_generator_majorant R m q k hKQ j d nu hNu (hDiameter j hj).
    exists a=> _; exact hA.
  - exists 0%R; by move=> h; case: (hj h).
pose a := fun j : J => projT1 (cid (hMajor j)).
have hA j (hj : G j) := projT2 (cid (hMajor j)) hj.
pose hm := euclidean_lebesgue_is_measure R m.
have hIntegral := @total_countable_nonnegative_integral R X J (@euclidean_lebesgue_measure R m) hm G
  rho (fun j => (a j)%:E) hG (fun j hj => (hA j hj).1) (fun j hj => (hA j hj).2.1).
have hNuCosts (j : closed_convex_euclidean_sets R q) : 0<= @integral_geometric_gauge R q k hKQ 1 (val j).
  exact: (@integral_geometric_gauge_nonnegative R q k hKQ 1 (lexx 1) (val j)
    (metric_borel_suslin (closed_borel_set (set_valP j).1))).
have hNuMeasure := metric_scale_envelope_is_measure hNu hNuCosts.
have hPoint y : nu [set z | A (@euclidean_block_join R m q (y,z))]<=
    nonnegative_sum G (fun j => rho j y).
  apply: le_trans (@measure_indexed_cover R Y J nu hNuMeasure _ G
    (fun j => [set z | S j (@euclidean_block_join R m q (y,z))]) hG _) _.
  - move=> z hz; have [j hj hJ] := hCover (@euclidean_block_join R m q (y,z)) hz.
    by exists j.
  - apply: nonnegative_sum_mono=> j hj; exact: (hA j hj).2.2.2 y.
have hAlmost : measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    (partial_extended_le_locus
      (partial_function_total (fun y : X => (nu [set z | A (@euclidean_block_join R m q (y,z))] : extended_real_line R)))
      (partial_function_total (fun y : X => (nonnegative_sum G (fun j => rho j y) : extended_real_line R)))).
  apply: (@measure_almost_everywhere_mono R X (@euclidean_lebesgue_measure R m) hm setT _ _
    (measure_almost_everywhere_true hm))=> y _.
  exists (nu [set z | A (@euclidean_block_join R m q (y,z))]),(nonnegative_sum G (fun j => rho j y)).
  split=> //; split=> //; exact: hPoint.
have hUpper := measure_upper_integral_monotone hm hAlmost.
have hValue := measure_upper_integral_unique (measure_upper_integral_specification _ _) hIntegral.2.1.
rewrite hValue in hUpper.
have hCosts : nonnegative_sum G (fun j => (a j)%:E)<=nonnegative_sum G c.
  apply: nonnegative_sum_mono=> j hj; exact: (hA j hj).2.2.1.
exact: le_trans hUpper (le_trans hCosts (ltW hCost)).
Qed.
