(** Federer (1969), 2.5.14, p. 107: every compact set has finite measure for
    a measure representing the integral on K(X), whether or not the compact
    set is measurable. Here containment in a positive strict level gives the
    same conclusion through 2.5.3. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactCutoffUP CompactCutoff
  FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeLevelMeasurability
  RealIntegralFunctionalUP MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_support_representing_measure_compact_finite]:
    compact finiteness in Federer 2.5.14, p. 107 This holds for every
    representing measure, so lattice regularity is unnecessary here. No
    measurability premise or conclusion for K is imposed. *)
Theorem compact_support_representing_measure_compact_finite (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (A : (X -> R) -> R) (hm : is_measure mu)
    (hA : is_real_integral_functional mu (@compactly_supported_continuous_functions R X) A) :
  hausdorff_space X -> locally_compact (@setT X) -> forall K, compact K -> mu K < +oo.
Proof.
move=> hh hl K hK.
pose u := @compact_cutoff R X K hh hl hK.
have hu := @compact_cutoff_specification R X K hh hl hK.
have ht : (0 < (2 : R)^-1)%R by rewrite invr_gt0 ltr0n.
have ht1 : ((2 : R)^-1 < 1)%R by rewrite invf_lt1 // ltr1n.
have hlevel : function_lattice_strict_levels (@compactly_supported_continuous_functions R X)
    [set x | ((2 : R)^-1 < u x)%R].
  exists u,((2 : R)^-1)%R; split; last by split.
  split; first exact: compact_cutoff_function hu.
  move=> x; exact: (andP (compact_cutoff_range hu x)).1.
have hfin := @represented_lattice_strict_level_finite R X _ A mu hm hA _ hlevel.
apply: le_lt_trans hfin; apply: (@measure_mono R X mu hm K _)=> x hx.
change (is_true (((2 : R)^-1 < u x)%R)).
rewrite /u (compact_cutoff_on_set hu hx); exact ht1.
Qed.
