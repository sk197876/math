(** Federer (1969), 2.5.3, p. 94: agreement on F0 determines agreement on F1
    and F2 by 2.1.3(4),(5). The lemmas here start from agreement on F0; the
    separate level-integral limit establishes that premise for representing
    measures. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeLevelFamilies FunctionLatticeLevelMeasurability
  RealIntegralFunctionalUP MeasureUP MeasureContinuityBelow MeasureContinuityAbove
  ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [represented_lattice_increasing_level_unique]: passage from
    F0 to F1 in Federer 2.5.3, p. 94, using 2.1.3(4), p. 55 Infinite union
    measures are allowed. *)
Lemma represented_lattice_increasing_level_unique (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (mu nu : set X -> \bar R)
    (hm : is_measure mu) (hn : is_measure nu)
    (hA : is_real_integral_functional mu L A) (hB : is_real_integral_functional nu L A) :
  (forall S, function_lattice_strict_levels L S -> mu S=nu S) ->
  forall S, function_lattice_increasing_levels L S -> mu S=nu S.
Proof.
move=> h0 S [V [hV [hmono ->]]].
have hmu n := @represented_lattice_strict_level_measurable R X L A mu hm hA (V n) (hV n).
have hnu n := @represented_lattice_strict_level_measurable R X L A nu hn hB (V n) (hV n).
have hlimu := @measure_continuity_below R X mu hm V hmu hmono.
have hlimv := @measure_continuity_below R X nu hn V hnu hmono.
have heq : (fun n => mu (V n))=(fun n => nu (V n)).
  apply: funext=> n; exact: h0 _ (hV n).
rewrite heq in hlimu.
exact: (extended_order_limit_unique hlimu.2 hlimv.2).
Qed.

(** Source for [represented_lattice_finite_hull_unique]: passage to F2 in
    Federer 2.5.3, p. 94, using 2.1.3(5), p. 55 Equality on F1 transfers
    finiteness of the first set to the second measure before continuity from
    above. *)
Lemma represented_lattice_finite_hull_unique (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (mu nu : set X -> \bar R)
    (hm : is_measure mu) (hn : is_measure nu)
    (hA : is_real_integral_functional mu L A) (hB : is_real_integral_functional nu L A) :
  (forall S, function_lattice_increasing_levels L S -> mu S=nu S) ->
  forall S, function_lattice_finite_hulls L mu S -> mu S=nu S.
Proof.
move=> h1 S [V [hV [hmono [hfin ->]]]].
have hmu n := @represented_lattice_increasing_level_measurable R X L A mu hm hA (V n) (hV n).
have hnu n := @represented_lattice_increasing_level_measurable R X L A nu hn hB (V n) (hV n).
have hfinv : nu (V 0%N) < +oo by rewrite -(h1 _ (hV 0%N)).
have hlimu := @measure_continuity_above R X mu hm V hmu hmono hfin.
have hlimv := @measure_continuity_above R X nu hn V hnu hmono hfinv.
have heq : (fun n => mu (V n))=(fun n => nu (V n)).
  apply: funext=> n; exact: h1 _ (hV n).
rewrite heq in hlimu.
exact: (extended_order_limit_unique hlimu.2 hlimv.2).
Qed.
