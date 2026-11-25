(** Corrected finite-exponent covering comparison for
    Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric CoveringFamilyUP MetricBoundedClosureLaws
  CompactConvexUniformReciprocalSecant CaratheodoryBoundedWeightedComparison
  IntegralGeometricGauge IntegralGeometricMeasure IntegralGeometricMeasureUP IntegralGeometricClosedCovers
  ProjectionBeta ProjectionMeasureUP ReciprocalExponent RealExponentialUP RealExponentialSealed
  TopologicalBorel BorelClosedProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_integral_geometric_reciprocal_bound]:
    corrected quantitative comparison supporting the finite-exponent
    continuity assertion in Federer 3.2.45, p. 279. One
    C>=0 gives beta_(1/u) Q_(1/u)(A) <=
    exp(C(v-u)/v) beta_(1/v) Q_(1/v)(A), for every
    0<=u<v<=1 and every original target A. The denominator
    v and the original Q measures are retained. The proof
    transfers the proved uniform compact-convex cost comparison
    through the closed-convex construction at finite cutoffs. *)
Theorem convex_integral_geometric_reciprocal_bound (R : realType) n m
    (hMN : (m <= n)%N) : exists C : R, (0 <= C)%R /\
  forall (u v : R) (A : set (inner_metric_space (@euclidean_inner_productP R n))),
    (0 <= u)%R -> (u < v)%R -> (v <= 1)%R ->
    (@projection_beta R n m hMN (reciprocal_lebesgue_exponent u))%:E *
      @convex_integral_geometric_measure R n m hMN (reciprocal_lebesgue_exponent u) A <=
    (@RealExponential.exponential R (C * (v-u)/v)%R)%:E *
      ((@projection_beta R n m hMN (reciprocal_lebesgue_exponent v))%:E *
        @convex_integral_geometric_measure R n m hMN (reciprocal_lebesgue_exponent v) A).
Proof.
have [C [hC hGauge]] := @compact_convex_uniform_reciprocal_secant R n m hMN.
exists C; split=> // u v A hU hUV hV1.
have hUE := @reciprocal_lebesgue_exponent_domain R u hU (le_trans (ltW hUV) hV1).
have hVE := @reciprocal_lebesgue_exponent_domain R v (le_trans hU (ltW hUV)) hV1.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose J := closed_convex_euclidean_sets R n.
pose c := fun j : J => @integral_geometric_gauge R n m hMN (reciprocal_lebesgue_exponent u) (val j).
pose d := fun j : J => @integral_geometric_gauge R n m hMN (reciprocal_lebesgue_exponent v) (val j).
pose a := @projection_beta R n m hMN (reciprocal_lebesgue_exponent u).
pose b := (RealExponential.exponential (C * (v-u)/v)%R *
  @projection_beta R n m hMN (reciprocal_lebesgue_exponent v))%R.
have hA : (0 < a)%R := @projection_beta_positive R n m hMN _ hUE.
have hB : (0 < b)%R.
  apply: mulr_gt0; first exact: (real_exponential_positive (@RealExponential.laws R) (C*(v-u)/v)%R).
  exact: (@projection_beta_positive R n m hMN _ hVE).
have hCostNonnegative j : 0 <= c j.
  apply: integral_geometric_gauge_nonnegative=> //.
  apply: metric_borel_suslin; exact: closed_borel_set (set_valP j).1.
have hCost j : metric_set_bounded (val j) -> a%:E*c j <= b%:E*d j.
  move=> hBound.
  have hCompact : compact (val j).
    have h := euclidean_bounded_closure_compact hBound.
    rewrite -(proj1 (closure_id (val j)) (set_valP j).1) in h; exact h.
  have h := hGauge (val j) u v hCompact (set_valP j).2 hU hUV hV1.
  by rewrite /a /b /c /d EFinM -muleA.
have h := @caratheodory_bounded_normalized_cost_comparison R X J (fun j => val j) c d
  (@convex_integral_geometric_measure R n m hMN (reciprocal_lebesgue_exponent u))
  (@convex_integral_geometric_measure R n m hMN (reciprocal_lebesgue_exponent v)) a b
  (@convex_integral_geometric_closed_cover_specification R n m hMN _ hUE)
  (@convex_integral_geometric_closed_cover_specification R n m hMN _ hVE)
  hCostNonnegative hA hB hCost A.
by rewrite /a /b EFinM -muleA in h.
Qed.
