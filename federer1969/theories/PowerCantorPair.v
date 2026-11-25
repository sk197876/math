(** Federer (1969), 2.10.28, p. 193: existence and all distribution-function
    conclusions for the power-gauge Cantor set. Normalisation c is arbitrary
    and positive; no identification with the pending real-degree
    Gamma-normalised Hausdorff measure is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals
  constructive_ereal topology num_normedtype lra.
From Federer Require Import RealMetricBackground MetricDiameterReal CompactIntervalGauge RealPower PowerConcaveIntervalGauge
  ConcaveIntervalMeasure EqualCostIntervalTreeUP EqualCostIntervalTree EqualCostIntervalTreeSpecial EqualCostCantorMass
  SpecialIntervalFamilyUP SpecialIntervalLimit ConcaveCantorFunction PowerCantorPairUP PowerCantorNull
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure RealCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [power_cantor_pair_exists]: direct
    existence of A(m,n) and its associated f
    in 2.10.28, p. 193. Compose only
    proved opaque interval-tree, limit and
    cumulative witnesses. The positive coefficient
    c is left explicit instead of assuming
    a real-degree Hausdorff normalisation formula. *)
Theorem power_cantor_pair_exists (R : realType) (c m : R) (n : nat -> nat) :
  0<c -> 0<m -> m<1 -> (forall j, (2<=n j)%N) ->
  exists A f, is_power_cantor_pair c m n A f.
Proof.
move=> hc hm hm1 hn.
have hg := @power_concave_interval_gauge R c m hc hm hm1.
have hunit : is_compact_real_interval (`[0,1] : set (real_line_metric R)) by exists 0,1; split.
pose J : compact_real_intervals R := Sub (`[0,1] : set (real_line_metric R)) (mem_set hunit).
have hJ : (0<fine (@MetricDiameter.extended_metric_diameter R [the metricType R of real_line_metric R] (val J)))%R.
  by rewrite /J /= (extended_metric_diameter_segment ler01) subr0.
pose H := @equal_cost_interval_tree R _ hg J n hJ hn.
have ht := @equal_cost_interval_tree_specification R _ hg J n hJ hn.
pose A := special_interval_tree_limit H.
have hA := @special_interval_tree_limit_specification R H.
have [f hf] := @concave_cantor_cumulative_exists R _ hg J n H A ht hA.
exists A,f; exists J,H; split=> //; split=> //; by split.
Qed.

(** Source for [power_cantor_pair_properties]: direct
    compactness, mass c, Holder estimate,
    both range identities, and derivative zero
    outside A and Lebesgue almost everywhere,
    in 2.10.28, p. 193. The pair
    is characterised only by its recursion
    and cumulative laws. The measure here
    is exactly the stated interval-generated
    c*t^m measure; real-degree Hausdorff
    identification is not asserted by this theorem. *)
Theorem power_cantor_pair_properties (R : realType) (c m : R) (n : nat -> nat)
    (A : set (real_line_metric R)) (f : R -> R) :
  0<c -> 0<m -> m<1 -> is_power_cantor_pair c m n A f ->
  compact A /\ A `<=` (`[0,1] : set (real_line_metric R)) /\
  concave_interval_measure (fun t=>c*real_power t m) A=c%:E /\
  (forall a b, a<=b -> 0<=f b-f a /\ f b-f a<=c*real_power (b-a) m) /\
  continuous (f : real_line_metric R -> real_line_metric R) /\
  f @` A=(`[0,c] : set R) /\ f @` setT=(`[0,c] : set R) /\
  lebesgue_scalar_measure A=0%E /\
  (forall x, ~A x -> has_real_curve_derivative f x 0) /\
  measure_almost_everywhere (@lebesgue_scalar_measure R) [set x | has_real_curve_derivative f x 0].
Proof.
move=> hc hm hm1 [J [H [hJ [ht [hA hf]]]]].
have hg := @power_concave_interval_gauge R c m hc hm hm1.
have [hcompact [hsub [hmass hbound]]] := @equal_cost_interval_limit_mass R _ hg J n H A ht hA.
have [hinc [hcont [hrangeA [hrange hderiv]]]] := @concave_cantor_cumulative_properties R _ hg J n H A f ht hA hf.
have hcost : concave_interval_cost (fun t=>c*real_power t m) (val J)=c.
  by rewrite hJ (concave_interval_cost_segment _ ler01) subr0 real_power_one_base mulr1.
have hnull := @power_interval_tree_limit_lebesgue_null R c m J H A hc hm hm1 hJ
  (equal_cost_tree_root ht) (@equal_cost_interval_tree_special R _ hg J n H ht) hA.
rewrite hcost in hmass hrangeA hrange.
rewrite hJ in hsub.
split=> //; split=> //; split=> //; split=> //; split=> //; split=> //; split=> //; split=> //; split=> //.
have hAE : measure_almost_everywhere (@lebesgue_scalar_measure R) (~` A).
  by rewrite /measure_almost_everywhere setCK hnull.
apply: (@measure_almost_everywhere_mono R R (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
  (~` A) [set x | has_real_curve_derivative f x 0] _ hAE)=> x hx.
exact: hderiv x hx.
Qed.
