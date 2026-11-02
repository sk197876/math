(** Federer (1969), 2.5.3, proof p. 95: controlling the integral of |h-a| by
    the integrals of h, a, and their common part. The identity below is a
    supporting equivalent form of the printed positive/negative part
    computation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureIntegralUP SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [real_absolute_difference_minimum]: supporting scalar
    identity for the error calculation in Federer 2.5.3, p. 95 This
    elementary identity is not separately numbered in either source. *)
Lemma real_absolute_difference_minimum (R : realType) (a b : R) :
  `|a-b|%R=(a+b-2*Order.min a b)%R.
Proof.
case: (leP a b)=> hab.
- rewrite ler0_norm ?subr_le0 // opprB mulr_natl mulr2n opprD addrA [(a+b)%R]addrC addrK.
  by [].
- rewrite ger0_norm ?subr_ge0 ?ltW // mulr_natl mulr2n opprD addrA addrK.
  by [].
Qed.

(** Source for [real_total_integral_absolute_difference_minimum]: integral
    form of the error estimate used in Federer 2.5.3, p. 95 Finiteness of
    all three displayed integrals is explicit. *)
Lemma real_total_integral_absolute_difference_minimum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> R) (a b c : R) :
  is_measure_integral mu (real_total_integrand f) a%:E ->
  is_measure_integral mu (real_total_integrand g) b%:E ->
  is_measure_integral mu (real_total_integrand (fun x => Order.min (f x) (g x))) c%:E ->
  is_measure_integral mu (real_total_integrand (fun x => `|f x-g x|%R)) (a+b-2*c)%R%:E.
Proof.
move=> hf hg hc.
have hs := @real_total_integral_add R X mu hm f g a b hf hg.
have hd := @real_total_integral_scale R X mu hm _ c 2%R hc.
have hi := @real_total_integral_subtract R X mu hm _ _ (a+b)%R (2*c)%R hs hd.
have he : (fun x => (f x+g x-2*Order.min (f x) (g x))%R)=(fun x => `|f x-g x|%R).
  apply: funext=> x; exact: esym (real_absolute_difference_minimum _ _).
by rewrite he in hi.
Qed.
