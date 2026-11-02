(** Federer (1969), 3.1.3(2), p. 213: strict rays of approximate upper
    and lower limits reduce to density-zero tests at rational thresholds.
    The definitions are those of 2.9.12, with the erratum's complements
    of closed-ray inverse images. No value is assigned by a default. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic MeasureSetDensity
  MeasureDerivationContext MeasureApproximateOrderLimits ExtendedRealBounds
  ExtendedRealOrderTopology LocalZeroDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [approximate_upper_limit_rational_ray]: the upper-limit
    part of the level-set argument in Federer 3.1.3(2), p. 213. Infimum
    laws and rational order density give an exact countable union.
    This supporting form also retains extended values and partial domains. *)
Theorem approximate_upper_limit_rational_ray (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (hc : is_measure_derivation_context phi V) (f : partial_function X (\bar R)) x t :
  measure_approximate_upper_limit phi V f x<t <->
  exists q : rat, (ratr q : R)%:E<t /\
    measure_approximate_upper_thresholds phi V f x (ratr q : R)%:E.
Proof.
split.
- move=> hlt; apply: contrapT=> hn.
  have hbound : t<=measure_approximate_upper_limit phi V f x.
    apply: extended_real_inf_greatest=> z hz.
    rewrite leNgt; apply/negP=> hzt.
    have [q [hzq hqt]] := @extended_rationals_order_dense R z t hzt.
    apply: hn; exists q; split=> //.
    apply: (@local_zero_density_mono R X phi V
      (~` partial_function_preimage f [set w | w<=(ratr q : R)%:E])
      (~` partial_function_preimage f [set w | w<=z])
      setT x hc openT I _ hz).
    move=> y _ hnq [w [hw hsmall]]; apply: hnq.
    exists w; split=> //; exact: le_trans hsmall (ltW hzq).
  by have := lt_le_trans hlt hbound; rewrite ltxx.
- move=> [q [hqt hq]].
  exact: le_lt_trans (extended_real_inf_lower hq) hqt.
Qed.

(** Source for [approximate_lower_limit_rational_ray]: the lower-limit
    part of Federer 3.1.3(2), p. 213, using the closed upper-ray
    complements in the corrected definition of 2.9.12. Infinite limits
    and undefined points remain explicit. *)
Theorem approximate_lower_limit_rational_ray (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (hc : is_measure_derivation_context phi V) (f : partial_function X (\bar R)) x t :
  t<measure_approximate_lower_limit phi V f x <->
  exists q : rat, t<(ratr q : R)%:E /\
    measure_approximate_lower_thresholds phi V f x (ratr q : R)%:E.
Proof.
split.
- move=> hlt; apply: contrapT=> hn.
  have hbound : measure_approximate_lower_limit phi V f x<=t.
    apply: extended_real_sup_least=> z hz.
    rewrite leNgt; apply/negP=> htz.
    have [q [htq hqz]] := @extended_rationals_order_dense R t z htz.
    apply: hn; exists q; split=> //.
    apply: (@local_zero_density_mono R X phi V
      (~` partial_function_preimage f [set w | (ratr q : R)%:E<=w])
      (~` partial_function_preimage f [set w | z<=w])
      setT x hc openT I _ hz).
    move=> y _ hnq [w [hw hlarge]]; apply: hnq.
    exists w; split=> //; exact: le_trans (ltW hqz) hlarge.
  by have := lt_le_trans hlt hbound; rewrite ltxx.
- move=> [q [htq hq]].
  exact: lt_le_trans htq (extended_real_sup_upper hq).
Qed.
