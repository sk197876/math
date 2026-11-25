(** Federer (1969), 2.5.14, p. 107, first two displays: open measurable
    outer approximation and compact measurable inner approximation of finite
    measurable sets. We use the already proved 2.5.3 envelope and supremum
    laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice CompactSupportLevels
  FunctionLatticeUP FunctionLatticeLevelMeasurability FunctionLatticeRegularityUP
  RegularDaniellEnvelope DaniellOuterRegularity DaniellInnerDifferenceSupremum
  RepresentedLatticeClosedLevels RealIntegralFunctionalUP MeasureUP MeasureBasic
  MeasureFiniteClosure ExtendedRealBoundsUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_support_regular_open_infimum]: first display of
    Federer 2.5.14, p. 107 All subsets, including those of infinite measure,
    are covered by the abstract infimum laws. *)
Theorem compact_support_regular_open_infimum (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (A : (X -> R) -> R) (hm : is_measure mu)
    (hA : is_real_integral_functional mu (@compactly_supported_continuous_functions R X) A)
    (hr : is_function_lattice_regular (@compactly_supported_continuous_functions R X) mu) (S : set X) :
  mu S = extended_real_inf
    [set a | exists V, open V /\ measure_measurable mu V /\ S `<=` V /\ a=mu V].
Proof.
have hL := @compactly_supported_continuous_functions_lattice R X.
have hc := @regular_representing_measure_envelope R X _ A hL mu hm hA hr.
have ho := @daniell_cover_lattice_outer_regular R X _ A mu hm hA hc.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: extended_real_inf_greatest=> a [V [_ [_ [hSV ->]]]]; exact: (@measure_mono R X mu hm S V hSV).
- apply: ho.2.2=> V hSV hV; apply: extended_real_inf_lower.
  exists V; split; first exact: compact_support_increasing_level_open hV.
  split; first exact: (@represented_lattice_increasing_level_measurable R X _ A mu hm hA V hV).
  by split.
Qed.

(** Source for [compact_support_regular_compact_supremum]: second display of
    Federer 2.5.14, p. 107 S must be measurable and have finite measure.
    Compact approximants are explicitly measurable; arbitrary compact sets
    are not silently assumed measurable. *)
Theorem compact_support_regular_compact_supremum (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (A : (X -> R) -> R) (hm : is_measure mu)
    (hA : is_real_integral_functional mu (@compactly_supported_continuous_functions R X) A)
    (hr : is_function_lattice_regular (@compactly_supported_continuous_functions R X) mu) (S : set X) :
  measure_measurable mu S -> mu S < +oo ->
  is_extended_real_supremum
    [set a | exists K, compact K /\ measure_measurable mu K /\ K `<=` S /\ a=mu K] (mu S).
Proof.
move=> hS hfin.
have hL := @compactly_supported_continuous_functions_lattice R X.
have hc := @regular_representing_measure_envelope R X _ A hL mu hm hA hr.
have hi := @daniell_inner_difference_supremum R X _ A hL mu hm hA hc S hS hfin.
constructor.
- move=> a [K [_ [_ [hKS ->]]]]; exact: (@measure_mono R X mu hm K S hKS).
- move=> b hb; apply: (extended_real_supremum_least hi)=> a [h [E [hh [hE [hsub ->]]]]].
  apply: hb; exists ([set x | (1 <= h x)%R] `\` E).
  split; first exact: compact_support_inner_difference_compact hh.1 hE.
  split.
  + apply: (@measure_measurable_difference R X mu hm).
    * exact: (@represented_lattice_closed_upper_level_measurable R X _ A mu hm hA h 1%R hh.1).
    * exact: (@represented_lattice_increasing_level_measurable R X _ A mu hm hA E hE).
  + by split.
Qed.
