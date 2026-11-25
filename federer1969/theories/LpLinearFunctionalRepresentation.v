(** Federer (1969), 2.5.7, pp. 98–99: representation of bounded linear
    functionals on the total scalar Lebesgue spaces. Erratum p. 2, book p.
    98 lines 10–11, requires the total-domain space and the closed unit
    ball; line 14 concerns countable measurability. The residual proof uses
    the corrections to book p. 99 lines 13, 14, and 17. The three printed
    exponent alternatives are packaged by is_lp_conjugate_pair, with
    countable measurability required only when q=infinity and increasing
    continuity required only when p=infinity. This is equivalent to the
    printed alternatives, including their endpoint hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP CountablyMeasurableUP FunctionLatticeSeminormUP FunctionOperatorSeminorm
  MonotoneDaniellIntegralUP ExtendedRealOrderLimit DaniellIntegralUP TotalScalarLpUP TotalScalarLpFiniteSeminorm
  TotalScalarLpFunctionalBounds FiniteLpLinearDaniell LpConjugatePair SignedLpDensityRepresentation
  LpFunctionalDensityUP LpFunctionalDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lp_bounded_linear_functional_is_daniell]: the preliminary
    Daniell conclusion in Federer 2.5.7, p. 98 For finite p continuity is
    proved by dominated convergence; only the infinity endpoint requires it
    as a separate hypothesis. *)
Theorem lp_bounded_linear_functional_is_daniell (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (A : (X -> R) -> R) :
  1 <= p -> is_linear_functional_on_functions (total_scalar_lp mu p) A ->
  function_operator_seminorm (total_scalar_lp mu p) A (finite_total_scalar_lp_norm mu p) < +oo ->
  (p=+oo -> forall f g, (forall n, total_scalar_lp mu p (f n)) -> total_scalar_lp mu p g ->
    real_functions_increase_to f g -> extended_order_limit (fun n => (A (f n))%:E) (A g)%:E) ->
  is_daniell_integral (total_scalar_lp mu p) A.
Proof.
case: p=> [p| |] hp hA hb hc; last by [].
- have hp' : (1 <= p)%R by move: hp; rewrite lee_fin.
  exact: (@finite_lp_bounded_linear_is_daniell R X mu hm p A hp' hA hb).
- exact: (@bounded_lp_linear_daniell_with_increasing_continuity R X mu hm +oo A hp hA hb (hc erefl)).
Qed.

(** Source for [lp_linear_functional_representation]: complete Federer
    2.5.7, pp. 98–99, with the stated erratum corrections The conclusions
    include an actual signed integral for every total Lp test, full Lq
    membership, exact corrected operator norm, and almost uniqueness. Zero
    measure and zero operator norm are included. *)
Theorem lp_linear_functional_representation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (A : (X -> R) -> R) :
  is_lp_conjugate_pair p q ->
  is_linear_functional_on_functions (total_scalar_lp mu p) A ->
  function_operator_seminorm (total_scalar_lp mu p) A (finite_total_scalar_lp_norm mu p) < +oo ->
  (q=+oo -> measure_countably_measurable mu setT) ->
  (p=+oo -> forall f g, (forall n, total_scalar_lp mu p (f n)) -> total_scalar_lp mu p g ->
    real_functions_increase_to f g -> extended_order_limit (fun n => (A (f n))%:E) (A g)%:E) ->
  is_daniell_integral (total_scalar_lp mu p) A /\
  exists k : X -> R, is_lp_functional_density mu p q A k /\
    total_scalar_lp_norm mu q k=function_operator_seminorm (total_scalar_lp mu p) A (finite_total_scalar_lp_norm mu p) /\
    forall l, is_lp_functional_density mu p q A l -> measure_almost_everywhere mu [set x | k x=l x].
Proof.
move=> hpq hA hb hX hc.
have hp := (lp_conjugate_pair_admissible hpq).1.
have hD := @lp_bounded_linear_functional_is_daniell R X mu hm p A hp hA hb hc.
split; first exact: hD.
have [M [_ [hM hbound]]] := @total_scalar_lp_functional_bound R X mu hm p A hp hA hb.
have [k [hk hrepr]] := @bounded_lp_daniell_density R X mu hm p q A M hpq hX hM hD hbound.
have hspec : is_lp_functional_density mu p q A k.
  apply: (proj2 (@lp_functional_density_pairing_equivalence R X mu hm p q A k hpq)); by split.
exists k; split; first exact: hspec.
split; first exact: (@lp_functional_density_norm R X mu hm p q A k hpq hspec).
move=> l hl; exact: (@lp_functional_density_almost_unique R X mu hm p q A k l hpq hspec hl).
Qed.
