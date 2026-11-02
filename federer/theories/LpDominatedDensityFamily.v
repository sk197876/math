(** Federer (1969), 2.5.7, p. 98: the family U of nonnegative Lq functions
    whose pairings on L+ are bounded above by mu+. The variation is an
    abstract functional P; its laws and norm bound are proved separately.
    The family definition does not assume any closure or maximal member. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FunctionLatticeUP TotalScalarLpUP TotalScalarLpClosure
  TotalScalarLpFiniteSeminorm TotalScalarLpFunctionalBounds TotalScalarPairingValue TotalScalarPairing
  TotalPositiveDualBound TotalLpPairingBound LpConjugatePair ConjugateExponents
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lp_dominated_density_family]: direct U in the proof of
    Federer 2.5.7, p. 98 The pairing value is used only for genuine
    conjugate Lp/Lq members in the consequences below. *)
Definition lp_dominated_density_family (R : realType) (X : choiceType)
    (mu : set X -> \bar R) p q (P : (X -> R) -> R) :=
  [set k : X -> R | total_scalar_lp mu q k /\ (forall x, (0 <= k x)%R) /\
    forall f, positive_function_lattice (total_scalar_lp mu p) f ->
      (total_scalar_pairing mu f k <= P f)%R].

(** Source for [zero_lp_dominated_density]: zero belongs to U in Federer
    2.5.7, p. 98 This includes the zero measure. *)
Lemma zero_lp_dominated_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (P : (X -> R) -> R) :
  1 <= q -> (forall f, positive_function_lattice (total_scalar_lp mu p) f -> (0 <= P f)%R) ->
  lp_dominated_density_family mu p q P (fun _ => 0%R).
Proof.
move=> hq hP; split; first exact: (@total_scalar_lp_zero R X mu hm q hq).
split; first by move=> x.
move=> f hf; rewrite (@total_scalar_pairing_zero_right R X mu hm f); exact: hP f hf.
Qed.

(** Source for [dominated_density_unit_pairing_bound]: the inequality
    integral f*u <= M phi_(p)(f), restricted to the unit ball, in Federer
    2.5.7, p. 98 P's real norm bound must be supplied, as proved for the
    positive variation in LpVariationBound.v. *)
Lemma dominated_density_unit_pairing_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (P : (X -> R) -> R) (u : X -> R) (M : R) :
  is_lp_conjugate_pair p q -> (0 <= M)%R ->
  (forall f, positive_function_lattice (total_scalar_lp mu p) f ->
    (P f <= M*finite_total_scalar_lp_norm mu p f)%R) ->
  lp_dominated_density_family mu p q P u -> nonnegative_total_pairing_bound mu p u M%:E.
Proof.
move=> hpq hM hP hu f hf hf0 hunit z hi.
have hri := @measure_integral_graph_equivalent R X mu _ _ z (total_scalar_product_integrand_graph u f) hi.
have hprod : positive_function_lattice (total_scalar_lp mu p) f by split.
have hb := le_trans (hu.2.2 f hprod) (hP f hprod).
have hN : (finite_total_scalar_lp_norm mu p f <= 1)%R.
  by rewrite (@total_scalar_lp_unit_ball_criterion R X mu hm p f hf).
have hNM : (M*finite_total_scalar_lp_norm mu p f <= M)%R.
  have hh := ler_wpM2l hM hN; by rewrite mulr1 in hh.
have he : (fun x => (u x*f x)%R)=(fun x => (f x*u x)%R).
  by apply: funext=> x; rewrite mulrC.
rewrite he in hri.
have hfi := (@total_lp_pairing_specification_and_bound R X mu hm p q f u hpq hf hu.1).1.
have hz := measure_integral_unique hri hfi.
rewrite hz lee_fin; exact: le_trans hb hNM.
Qed.

(** Source for [lp_dominated_density_norm_bound]: the complete bound
    phi_(q)(u)<=M for u in U, Federer 2.5.7, p. 98 All three exponent pairs
    use the already proved dual supremum theorem. *)
Theorem lp_dominated_density_norm_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (P : (X -> R) -> R) (u : X -> R) (M : R) :
  is_lp_conjugate_pair p q -> (0 <= M)%R ->
  (forall f, positive_function_lattice (total_scalar_lp mu p) f ->
    (P f <= M*finite_total_scalar_lp_norm mu p f)%R) ->
  lp_dominated_density_family mu p q P u -> total_scalar_lp_norm mu q u <= M%:E.
Proof.
move=> hpq hM hP hu.
have hb := @dominated_density_unit_pairing_bound R X mu hm p q P u M hpq hM hP hu.
have hc := hu.1.2.2.2.
case: hpq hb hu hc=> [[a [ha [-> ->]]]|[[-> ->]|[-> ->]]] hb hu hc.
- apply: (@positive_finite_density_norm_bound R X mu hm (finite_conjugate_exponent a) u M%:E
    (finite_conjugate_exponent_strict ha) hu.2.1 hc).
  by rewrite (finite_conjugate_exponent_involutive ha).
- exact: (@positive_linfinity_density_norm_bound R X mu hm u M%:E hu.2.1 hc hb).
- exact: (@positive_lone_density_norm_bound R X mu hm u M%:E hu.2.1 hc hb).
Qed.
