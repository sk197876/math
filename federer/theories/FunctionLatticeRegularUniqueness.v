(** Federer (1969), 2.5.3, p. 94: the representing measure is characterised
    by L regularity. These consequences use Federer's finite-hull definition
    of regularity, keeping it distinct. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeRegularityUP
  FunctionLatticeFiniteHullLaws FunctionLatticeLevelIntegral FunctionLatticeLevelUniqueness
  RealIntegralFunctionalUP MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [function_lattice_regular_measure_dominates]: supporting
    maximality in the characterisation of Federer 2.5.3, p. 94 Agreement on
    the finite hulls gives domination on every subset, including subsets of
    infinite measure. *)
Lemma function_lattice_regular_measure_dominates (R : realType) (X : choiceType)
    (L : set (X -> R)) (mu nu : set X -> \bar R) (hn : is_measure nu) :
  is_function_lattice_regular L mu ->
  (forall W, function_lattice_finite_hulls L mu W -> mu W=nu W) ->
  forall S, nu S <= mu S.
Proof.
move=> hr he S; case: (ltP (mu S) +oo)=> hfin.
- have [W [hSW [hW [hval hWfin]]]] := (hr S).1 hfin.
  rewrite hval (he W hW); exact: (@measure_mono R X nu hn S W hSW).
- apply: le_trans (leey (nu S)) hfin.
Qed.

(** Source for [function_lattice_regular_representation_maximal]: maximality
    of an L regular representing measure in the characterisation of Federer
    2.5.3, p. 94 Existence of the regular measure is a separate theorem. *)
Theorem function_lattice_regular_representation_maximal (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (hA : is_real_integral_functional mu L A) (hB : is_real_integral_functional nu L A) :
  is_function_lattice_regular L mu -> forall S, nu S <= mu S.
Proof.
move=> hr.
have h0 := @represented_lattice_strict_level_unique R X L A hL mu nu hm hn hA hB.
have h1 := @represented_lattice_increasing_level_unique R X L A mu nu hm hn hA hB h0.
have h2 := @represented_lattice_finite_hull_unique R X L A mu nu hm hn hA hB h1.
exact: (@function_lattice_regular_measure_dominates R X L mu nu hn hr h2).
Qed.

(** Source for [function_lattice_regular_representation_unique]: uniqueness
    in the L regular characterisation of Federer 2.5.3, p. 94 This follows
    by applying the proved maximality in both directions. *)
Theorem function_lattice_regular_representation_unique (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (hA : is_real_integral_functional mu L A) (hB : is_real_integral_functional nu L A) :
  is_function_lattice_regular L mu -> is_function_lattice_regular L nu ->
  forall S, mu S=nu S.
Proof.
move=> hr hs S.
have hle := @function_lattice_regular_representation_maximal R X L A hL nu mu hn hm hB hA hs S.
have hge := @function_lattice_regular_representation_maximal R X L A hL mu nu hm hn hA hB hr S.
by apply/eqP; rewrite eq_le hle hge.
Qed.
