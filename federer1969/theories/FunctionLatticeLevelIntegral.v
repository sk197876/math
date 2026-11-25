(** Federer (1969), 2.5.3, p. 94, first display: the strict-level measure is
    determined by normalised truncation integrals. This module proves the
    limit along reciprocal widths 1/(n+1), sufficient for the uniqueness
    argument; the printed arbitrary-width right limit is a separate
    assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeRamp FunctionLatticeLevelFamilies
  FunctionLatticeLevelRamps FunctionLatticeLevelMeasurability RealIntegralFunctionalUP
  SummableRealFunctionUP RealTotalIntegralLimits RealTotalCharacteristicBounds
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureCharacteristicIntegral
  MeasureUP MeasureIncreasingConvergence PartialFunctionLimitExtremaUP ExtendedRealOrderLimit
  ExtendedIncreasingLimitSupremum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [represented_lattice_strict_level_integral_limit]:
    reciprocal-width case of the first limit in Federer 2.5.3, p. 94 This
    supporting sequence limit uses each actual integral witness and does not
    assume uniqueness or regularity of the representing measure. *)
Theorem represented_lattice_strict_level_integral_limit (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hA : is_real_integral_functional mu L A) (f : X -> R) (t : R) :
  positive_function_lattice L f -> (0 < t)%R ->
  extended_increases_to
    (fun n => (A (real_lattice_ramp f t (t+((n.+1)%:R)^-1)%R))%:E)
    (mu [set x | (t < f x)%R]).
Proof.
move=> hf ht.
pose S := [set x | (t < f x)%R].
pose s := @CharacteristicFunction.value R X S.
have hs := @CharacteristicFunction.laws R X S.
pose u n := real_lattice_ramp f t (t+((n.+1)%:R)^-1)%R.
have hp n : positive_function_lattice L (u n).
  apply: (@real_lattice_ramp_member R X L hL f t (t+((n.+1)%:R)^-1)%R hf.1 (ltW ht)).
  by rewrite ltrDl invr_gt0 ltr0n.
have hinc := @real_lattice_reciprocal_level_ramps_increase R X f t s hs.
have hlim : is_partial_function_lower_limit (fun n => real_total_integrand (u n)) (real_total_integrand s).
  apply: real_total_pointwise_lower_limit=> x; exact: (hinc x).2.
have hS : function_lattice_strict_levels L S by exists f,t; split=> //; split.
have hmeas := @represented_lattice_strict_level_measurable R X L A mu hm hA S hS.
have hchar := @measure_characteristic_integral R X mu hm S s hs hmeas.
apply: (@measure_increasing_integral_values R X mu hm
  (fun n => real_total_integrand (u n)) (real_total_integrand s)
  (fun n => (A (u n))%:E) (mu S) hlim).
- move=> n; exact: (@real_total_nonnegative_almost R X mu hm (u n) (hp n).2).
- move=> n; apply: (@real_total_pointwise_order_almost R X mu hm (u n) (u n.+1))=> x.
  have h := (hinc x).1 n n.+1 (leqnSn n); by move: h; rewrite lee_fin.
- move=> n; exact: (hA _ (hp n).1).
- exact hchar.
Qed.

(** Source for [represented_lattice_strict_level_unique]: uniqueness on F0
    in Federer 2.5.3, p. 94 Both representing measures are limits of the
    same normalised functional values. *)
Theorem represented_lattice_strict_level_unique (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (hA : is_real_integral_functional mu L A) (hB : is_real_integral_functional nu L A) :
  forall S, function_lattice_strict_levels L S -> mu S=nu S.
Proof.
move=> S [f [t [hf [ht ->]]]].
have hu := @represented_lattice_strict_level_integral_limit R X L A hL mu hm hA f t hf ht.
have hv := @represented_lattice_strict_level_integral_limit R X L A hL nu hn hB f t hf ht.
exact: (extended_order_limit_unique hu.2 hv.2).
Qed.
