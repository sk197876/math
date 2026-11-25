(** Federer (1969), 2.5.7, pp. 98–99: M equals the Lq norm of the
    representing density, using 2.4.16. M uses the corrected closed unit
    ball from erratum p. 2, book p. 98 line 11. No positivity of the density
    or the represented functional is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP ExtendedRealBoundsUP
  MeasureFiniteDuality MeasureLoneDuality MeasureLinfinityDuality ConjugateExponents
  FunctionOperatorSeminorm TotalScalarLpUP TotalScalarLpNormLaws TotalScalarLpFiniteSeminorm
  TotalScalarPairingValue TotalLpPairingBound LpConjugatePair RepresentedFunctionalDualBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [representing_density_norm_lower_bound]: the Lq norm is
    bounded by M via the sign-matching dual suprema, Federer 2.5.7, p. 99
    This includes both endpoint exponent pairs. *)
Lemma representing_density_norm_lower_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (A : (X -> R) -> R) (k : X -> R) :
  is_lp_conjugate_pair p q -> total_scalar_lp mu q k ->
  (forall f, total_scalar_lp mu p f -> A f=total_scalar_pairing mu f k) ->
  total_scalar_lp_norm mu q k <= function_operator_seminorm (total_scalar_lp mu p) A (finite_total_scalar_lp_norm mu p).
Proof.
move=> hpq hk hrep.
case: hpq hk hrep=> [[a [ha [-> ->]]]|[[-> ->]|[-> ->]]] hk hrep.
- have hs := (@finite_dual_supremum R X mu hm (finite_conjugate_exponent a) k
    (finite_conjugate_exponent_strict ha) hk.2.2.2).2.
  rewrite (finite_conjugate_exponent_involutive ha) in hs.
  apply: (extended_real_supremum_least hs).
  apply: (@represented_finite_sign_test_bound R X mu hm a (finite_conjugate_exponent a)%:E A k _ hk hrep).
  left; exists a; by split=> //; split.
- have hs := (@linfinity_dual_supremum R X mu hm k hk.2.2.2).2.
  apply: (extended_real_supremum_least hs).
  apply: (@represented_finite_sign_test_bound R X mu hm 1%R +oo A k _ hk hrep).
  by right; left.
- have hs := (@lone_dual_supremum R X mu hm (total_scalar_function k) hk.2.2.2).2.
  apply: (extended_real_supremum_least hs).
  apply: (@represented_infinity_sign_test_bound R X mu hm 1 A k _ hk hrep).
  by right; right.
Qed.

(** Source for [representing_density_operator_norm]: exact norm identity
    M=phi_(q)(k) in Federer 2.5.7, pp. 98–99 Representation itself implies
    finiteness of M, because k is in Lq. *)
Theorem representing_density_operator_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (A : (X -> R) -> R) (k : X -> R) :
  is_lp_conjugate_pair p q -> total_scalar_lp mu q k ->
  (forall f, total_scalar_lp mu p f -> A f=total_scalar_pairing mu f k) ->
  function_operator_seminorm (total_scalar_lp mu p) A (finite_total_scalar_lp_norm mu p)=total_scalar_lp_norm mu q k.
Proof.
move=> hpq hk hrep; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite -(@finite_total_scalar_lp_norm_exact R X mu hm q k hk).
  apply: function_operator_seminorm_least_bound.
  + apply: fine_ge0; exact: (@total_scalar_lp_norm_nonnegative R X mu hm q k hk.1 hk.2.1).
  + move=> f hf; rewrite (hrep f hf) mulrC.
    exact: (@total_lp_pairing_specification_and_bound R X mu hm p q f k hpq hf hk).2.
- exact: (@representing_density_norm_lower_bound R X mu hm p q A k hpq hk hrep).
Qed.
