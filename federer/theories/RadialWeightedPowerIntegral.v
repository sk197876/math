(** Federer (1969), 3.2.35, p. 272:
    integrate the actual nonnegative intrinsic-volume
    weights against the natural radius powers. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealOpenIntervals RadialNaturalPowerIntegral LebesgueScalarMeasure
  ExtendedRealOrderTopology PartialFunctionBasic PartialZeroExtension SummableRealFunctionUP
  MeasureSubsetIntegral MeasureIntegralGraphEquivalence SubsetFiniteNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radial_weighted_power_integral]: the
    weighted natural-power integration in the
    last line of Federer 3.2.35, p. 272.
    The actual scalar monomial integral and
    proved subset homogeneity apply on the
    original positive interval. The coefficient
    may be any nonnegative extended number;
    values outside the interval are irrelevant. *)
Lemma radial_weighted_power_integral (R:realType) j (r:R) (c: \bar R):
  (0<r)%R ->0<=c ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) (real_open_interval 0 r)
    (partial_function_total (fun t:R=>(c*(t^+j)%R%:E:extended_real_line R)))
    (c*(r^+j.+1/j.+1%:R)%R%:E).
Proof.
move=>hr hc.
have hPower:=@radial_natural_power_integral R j r hr.
have hTotal:is_measure_subset_integral (@lebesgue_scalar_measure R) (real_open_interval 0 r)
    (partial_function_total (fun t:R=>((t^+j)%R%:E:extended_real_line R))) (r^+j.+1/j.+1%:R)%R%:E.
  apply:(measure_integral_graph_equivalent _ hPower)=>t z.
  case:(pselect (real_open_interval 0 r t))=>ht.
  - rewrite !(partial_function_zero_extension_on _ _ _ ht) real_total_integrand_graph.
    reflexivity.
  - by rewrite !(partial_function_zero_extension_off _ _ _ ht).
have hNonnegative (t:R):real_open_interval 0 r t ->0<=(t^+j)%R%:E.
  move=>[ht0 _]; rewrite lee_fin; apply:exprn_ge0; exact:ltW ht0.
exact:(@subset_nonnegative_extended_scale_integral R R (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) (real_open_interval 0 r)
  (fun t:R=>((t^+j)%R%:E:extended_real_line R)) _ c hNonnegative hc hTotal).
Qed.
