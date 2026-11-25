(** Federer (1969), 2.5.7, pp. 98–99: the product pairing is defined on
    every conjugate pair of total Lebesgue spaces and is bounded by the
    product of their norms. These consequences use the existing sealed
    integral value. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureIntegralUP SummableRealFunctionUP ConjugateExponents
  TotalScalarLpUP TotalScalarLpFiniteSeminorm TotalScalarPairing TotalScalarFinitePairing
  TotalScalarPairingValue LpConjugatePair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_lp_pairing_integral_bound]: complete Holder estimate
    needed for the pairings in Federer 2.5.7, pp. 98–99 Zero norms and both
    endpoints are included. *)
Theorem total_lp_pairing_integral_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (f g : X -> R) :
  is_lp_conjugate_pair p q -> total_scalar_lp mu p f -> total_scalar_lp mu q g ->
  exists c : R, is_measure_integral mu (real_total_integrand (fun x => (f x*g x)%R)) c%:E /\
    (`|c| <= finite_total_scalar_lp_norm mu p f*finite_total_scalar_lp_norm mu q g)%R.
Proof.
move=> [[a [ha [-> ->]]]|[[-> ->]|[-> ->]]] hf hg.
- exact: (@total_scalar_pairing_finite_exponents R X mu hm a (finite_conjugate_exponent a) f g
    (finite_conjugate_exponent_reciprocals ha) hf hg).
- exact: (@total_scalar_pairing_lone_linfinity R X mu hm f g hf hg).
- have [c [hci hc]] := @total_scalar_pairing_lone_linfinity R X mu hm g f hg hf.
  have he : (fun x => (g x*f x)%R)=(fun x => (f x*g x)%R) by apply: funext=> x; rewrite mulrC.
  exists c; split; first by rewrite -he.
  by rewrite mulrC.
Qed.

(** Source for [total_lp_pairing_specification_and_bound]: the actual sealed
    integral value obeys Holder's bound in Federer 2.5.7, pp. 98–99 This
    also establishes product summability, rather than assuming it. *)
Theorem total_lp_pairing_specification_and_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (f g : X -> R) :
  is_lp_conjugate_pair p q -> total_scalar_lp mu p f -> total_scalar_lp mu q g ->
  is_measure_integral mu (real_total_integrand (fun x => (f x*g x)%R)) (total_scalar_pairing mu f g)%:E /\
    (`|total_scalar_pairing mu f g| <= finite_total_scalar_lp_norm mu p f*finite_total_scalar_lp_norm mu q g)%R.
Proof.
move=> hpq hf hg.
have [c [hi hc]] := @total_lp_pairing_integral_bound R X mu hm p q f g hpq hf hg.
have he := @total_scalar_pairing_value_of_integral R X mu f g c hi.
by rewrite he; split.
Qed.
