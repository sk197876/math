(** Federer (1969), 2.5.3, p. 94, first paragraph: every measure phi
    satisfying the conclusion of 2.5.2 satisfies the displayed formula for
    phi{x : f(x) > t}; "Thus lambda uniquely determines the restriction of
    phi to the class F0 of all these sets {x : f(x) > t}; using 2.1.3(4) and
    (5), we infer the same for the classes" F1 and F2. This module states
    the whole assertion for two representing measures in one theorem,
    composing the separate steps proved in FunctionLatticeLevelIntegral.v,
    FunctionLatticeLevelUniqueness.v and FunctionLatticeFiniteHullLaws.v.
    Since F2 is defined with the condition phi(A_1) < oo, the theorem also
    records that F2 is the same class for both measures. The local erratum
    has no entry for p. 94. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeLevelIntegral
  FunctionLatticeLevelUniqueness FunctionLatticeFiniteHullLaws FunctionLatticeLevelRightLimit
  FunctionLatticeLayers PositiveRightOrderLimit RealIntegralFunctionalUP MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [represented_lattice_level_families_agree]: Federer
    2.5.3, p. 94: any two measures phi and phi' satisfying the
    conclusion of 2.5.2 for (L, lambda), namely
    lambda(f) = integral f dphi = integral f dphi' whenever f in L,
    agree on F0 and on F1; the class F2 defined with phi equals the
    class F2 defined with phi', and phi and phi' agree on it. Neither
    measure is assumed L regular. *)
Theorem represented_lattice_level_families_agree (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu) :
  is_real_integral_functional mu L A -> is_real_integral_functional nu L A ->
  [/\ forall S, function_lattice_strict_levels L S -> mu S = nu S,
    forall S, function_lattice_increasing_levels L S -> mu S = nu S,
    function_lattice_finite_hulls L mu = function_lattice_finite_hulls L nu &
    forall S, function_lattice_finite_hulls L mu S -> mu S = nu S].
Proof.
move=> hA hB.
have h0 := @represented_lattice_strict_level_unique R X L A hL mu nu hm hn hA hB.
have h1 := @represented_lattice_increasing_level_unique R X L A mu nu hm hn hA hB h0.
split=> //.
- exact: function_lattice_finite_hulls_measure_independent h1.
- exact: (@represented_lattice_finite_hull_unique R X L A mu nu hm hn hA hB h1).
Qed.

(** Source for [represented_lattice_level_determination]: the first
    paragraph of Federer 2.5.3, p. 94, as one statement: every
    measure phi with lambda(f) = integral f dphi for f in L satisfies
    phi{x : f(x) > t} = lim_(h -> 0+) h^-1 lambda[inf{f, t+h} - inf{f, t}]
    whenever f in L+ and t > 0, and every other such measure has the same
    restrictions to F0, F1 and F2. *)
Theorem represented_lattice_level_determination (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_real_integral_functional mu L A ->
  (forall (f : X -> R) (t : R), positive_function_lattice L f -> (0 < t)%R ->
    positive_right_extended_order_limit
      (fun h => (h^-1 * A (real_lattice_layer f t (t+h)%R))%R%:E)
      (mu [set x | (t < f x)%R])) /\
  forall nu : set X -> \bar R, is_measure nu -> is_real_integral_functional nu L A ->
    [/\ forall S, function_lattice_strict_levels L S -> mu S = nu S,
      forall S, function_lattice_increasing_levels L S -> mu S = nu S,
      function_lattice_finite_hulls L mu = function_lattice_finite_hulls L nu &
      forall S, function_lattice_finite_hulls L mu S -> mu S = nu S].
Proof.
move=> hA; split.
- move=> f t hf ht.
  exact: (@represented_lattice_strict_level_right_limit R X L A hL mu hm hA f t hf ht).
- move=> nu hn hB.
  exact: (@represented_lattice_level_families_agree R X L A hL mu nu hm hn hA hB).
Qed.
