(** Federer (1969), 2.5.14, p. 107, first paragraph: when the topology has a
    countable base, the K(X)-regular representing measure is Radon. We prove
    the forward implication asserted by Federer, using compact unit levels
    for inner regularity also at infinite mass. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice CompactSupportLevels
  CompactSupportMeasureFinite CompactSupportMeasureRegularity CompactSupportOpenBase
  FunctionLatticeUP FunctionLatticeLevelMeasurability FunctionLatticeRegularityUP
  FunctionLatticeUnionInnerApproximation RealIntegralFunctionalUP MeasureUP MeasureBasic
  ExtendedRealBoundsUP ExtendedRealBounds RadonMeasureUP CountableOpenBaseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_support_regular_countable_base_radon]: the
    countable-base conclusion in Federer 2.5.14, p. 107 No sigma-finiteness
    is assumed. Inner regularity is established for every open set,
    including those of infinite measure. *)
Theorem compact_support_regular_countable_base_radon (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (A : (X -> R) -> R) (hm : is_measure mu)
    (hA : is_real_integral_functional mu (@compactly_supported_continuous_functions R X) A)
    (hr : is_function_lattice_regular (@compactly_supported_continuous_functions R X) mu)
    (B : nat -> set X) : hausdorff_space X -> locally_compact (@setT X) ->
  is_countable_open_base B -> is_radon_measure mu.
Proof.
move=> hh hl hB.
have hlevel := @compact_support_open_is_increasing_level R X B hh hl hB.
constructor=> //.
- exact: (@compact_support_representing_measure_compact_finite R X mu A hm hA hh hl).
- move=> V hV; exact: (@represented_lattice_increasing_level_measurable R X _ A mu hm hA V (hlevel V hV)).
- move=> V hV c hc.
  have hs := @represented_lattice_union_inner_supremum R X _ A
    (@compactly_supported_continuous_functions_lattice R X) mu hm hA V (hlevel V hV).
  apply: (extended_real_supremum_least hs)=> a [h [hh' [hsub ->]]].
  apply: hc=> //; exact: (@compact_support_positive_closed_level_compact R X h 1%R hh'.1 (@ltr01 R)).
- move=> S c hc; rewrite (@compact_support_regular_open_infimum R X mu A hm hA hr S).
  apply: extended_real_inf_greatest=> a [V [hV [_ [hSV ->]]]]; exact: hc V hV hSV.
Qed.
