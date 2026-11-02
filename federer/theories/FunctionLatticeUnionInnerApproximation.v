(** Federer (1969), 2.5.3, pp. 94–95: inner approximation by lattice levels.
    These are supporting statements, and do not replace Federer's larger
    difference-set class. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeInnerLevels
  FunctionLatticeLevelMeasurability FunctionLatticeStrictInnerApproximation RealIntegralFunctionalUP
  MeasureUP MeasureBasic MeasureContinuityBelow ExtendedRealBoundsUP ExtendedRealLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [represented_lattice_union_inner_supremum]: Supporting
    Federer 2.5.3, p. 94.Infinite F1 measure is allowed. *)
Theorem represented_lattice_union_inner_supremum (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) (hA : is_real_integral_functional mu L A)
    (V : set X) : function_lattice_increasing_levels L V ->
  is_extended_real_supremum (function_lattice_inner_unit_values L mu V) (mu V).
Proof.
move=> hV; constructor.
- move=> a [h [hh [hsub ->]]]; exact: (@measure_mono R X mu hm _ V hsub).
- move=> b hb; have [U [hU [hmono hVU]]] := hV.
  have hmeas n := @represented_lattice_strict_level_measurable R X L A mu hm hA (U n) (hU n).
  have hlim := @measure_continuity_below R X mu hm U hmeas hmono.
  rewrite hVU; apply: (extended_order_limit_upper_bound hlim.2)=> n.
  apply: (@represented_lattice_strict_inner_upper_bound R X L A hL mu hm hA (U n) b (hU n)).
  move=> a [h [hh [hsub heq]]]; apply: hb; exists h; split=> //; split=> //.
  move=> x hx; rewrite hVU; exists n=> //; exact: hsub x hx.
Qed.

(** Source for [represented_lattice_union_inner_approximation]: Supporting
    Federer 2.5.3, proof p. 95. *)
Lemma represented_lattice_union_inner_approximation (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) (hA : is_real_integral_functional mu L A)
    (V : set X) (r : \bar R) : function_lattice_increasing_levels L V -> r < mu V ->
  exists h : X -> R, positive_function_lattice L h /\
    [set x | (1 <= h x)%R] `<=` V /\ r < mu [set x | (1 <= h x)%R].
Proof.
move=> hV hr; apply: contrapT=> hnone.
have hs := @represented_lattice_union_inner_supremum R X L A hL mu hm hA V hV.
have hb : mu V <= r.
  apply: (extended_real_supremum_least hs)=> a [h [hh [hsub ->]]].
  rewrite leNgt; apply/negP=> hlt; apply: hnone; exists h; by split=> //; split.
by move: hr; rewrite ltNge hb.
Qed.
