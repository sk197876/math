(** Federer (1969), 3.2.13, p. 250: the
    nonnegative radial test r^(m-1) on (0,1)
    has finite integral 1/m. Zero
    completion at both excluded endpoints respects
    the existing degree-zero convention. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import UnitPowerIntegral LebesgueOpenSegmentIntegral RealSubsetIntegralGraph
  LebesgueScalarMeasure MeasureIntegralUP PartialFunctionUP PartialFunctionBasic MeasureIntegralGraphEquivalence
  SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_unit_radial_power]: the radial
    factor restricted to 0<r<1 in
    the sphere-mass deduction of Federer 3.2.13,
    p. 250. Both endpoints are explicitly zeroed. *)
Definition positive_unit_radial_power (R:realType) k (r:R):R:=
  if 0<r<1 then r^+k else 0.

(** Source for [positive_unit_radial_power_nonnegative]: the
    unit-ball radial test is nonnegative, including
    degree zero, supporting Federer 3.2.13, p. 250. *)
Lemma positive_unit_radial_power_nonnegative (R:realType) k (r:R):
  0<=positive_unit_radial_power k r.
Proof.
rewrite /positive_unit_radial_power; case:ifP=>h; last exact:lexx.
exact (exprn_ge0 k (ltW (andP h).1)).
Qed.

(** Source for [positive_unit_radial_power_integral]: exact
    completed radial integral in the sphere-mass
    computation, Federer 3.2.13, p. 250,
    using the proved polynomial integral and null
    endpoint removal. No sphere mass enters this proof. *)
Lemma positive_unit_radial_power_integral (R:realType) k:
  is_measure_integral (@lebesgue_scalar_measure R)
    (partial_function_total (fun r:R=>((positive_unit_radial_power k r)%:E:extended_real_line R)))
    (k.+1%:R^-1)%:E.
Proof.
have hOpen:=lebesgue_closed_open_segment_integral (@unit_natural_power_integral R k).
have hReal:is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (@positive_unit_radial_power R k)) (k.+1%:R^-1)%:E.
  apply:((@real_subset_integral_total R R (@lebesgue_scalar_measure R) `]0,1[
    (fun r:R=>r^+k) (@positive_unit_radial_power R k) (k.+1%:R^-1)%:E _ _).1 hOpen).
  - move=>r; rewrite /= in_itv /= =>h; by rewrite /positive_unit_radial_power h.
  - move=>r h; rewrite /positive_unit_radial_power; case:ifP=>h0; last by [].
    exfalso; apply:h; by rewrite /= in_itv /=.
apply:measure_integral_graph_equivalent _ hReal=>r z.
by rewrite real_total_integrand_graph.
Qed.
