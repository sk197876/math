(** Federer (1969), 2.5.10, p. 101: continuity used to pass from finite
    unions to all summable tests. The bounded L1 functional is Daniell by
    2.5.7, p. 98, and annihilates zero-norm functions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP FunctionLatticeSeminormUP FunctionOperatorSeminorm
  DaniellIntegralUP TotalScalarLpUP TotalScalarLpFiniteSeminorm FiniteLpLinearDaniell LpNullRespectingFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_lone_functional_continuity]: supporting
    Daniell continuity and almost-equality invariance for Federer
    2.5.10, p. 101, derived from 2.5.7, p. 98.
    A zero bound is permitted. *)
Lemma bounded_lone_functional_continuity (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : (X -> R) -> R) (M : R) :
  (0 <= M)%R -> is_linear_functional_on_functions (total_scalar_lp mu 1) A ->
  (forall f, total_scalar_lp mu 1 f -> (`|A f| <= M * finite_total_scalar_lp_norm mu 1 f)%R) ->
  is_daniell_integral (total_scalar_lp mu 1) A /\
    forall f g, total_scalar_lp mu 1 f -> total_scalar_lp mu 1 g ->
      measure_almost_everywhere mu [set x | f x=g x] -> A f=A g.
Proof.
move=> hM hA hb; split.
- have hop := @function_operator_seminorm_least_bound R X _ A _ M hM hb.
  exact: (@finite_lp_bounded_linear_is_daniell R X mu hm 1%R A (lexx _) hA (le_lt_trans hop (ltry M))).
- apply: (@lp_null_respecting_functional_almost_equal R X mu hm 1 A (lexx _) hA)=> f hf hn.
  have hh := hb f hf.
  rewrite /finite_total_scalar_lp_norm hn fine0 mulr0 normr_le0 in hh.
  exact: (elimT eqP hh).
Qed.
