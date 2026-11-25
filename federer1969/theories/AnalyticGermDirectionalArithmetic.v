(** Supporting Federer (1969), 3.4.8(5), p. 328:
    actual divided directional coefficients preserve
    zero, addition and finite sums. This is the
    derivative arithmetic of 3.4.5, p. 319,
    applied before the radial factorisation argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermUP AnalyticGermRing AnalyticGermJetsSealed AnalyticGermJetArithmetic
  AnalyticGermJetZeroNegate AnalyticGermDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Arithmetic.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Variable a:X.
Variable k:nat.
Variable v:X.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
Local Notation c:=(@analytic_germ_directional_coefficient R X NX hNX a k).

(** Source for [analytic_germ_directional_zero]: the
    actual zero germ has zero divided coefficients,
    supporting 3.4.8(5), p. 328, from 3.4.5, p. 319. *)
Lemma analytic_germ_directional_zero:c 0 v = 0.
Proof. by rewrite /analytic_germ_directional_coefficient analytic_germ_jet_zero linear0 mulr0. Qed.

(** Source for [analytic_germ_directional_add]: actual
    divided derivatives preserve the original germ sum,
    supporting the same assertions, pp. 319, 328. *)
Lemma analytic_germ_directional_add (alpha beta:G):c (alpha+beta) v = c alpha v+c beta v.
Proof.
by rewrite /analytic_germ_directional_coefficient analytic_germ_jet_add linearD /= mulrDr.
Qed.

(** Source for [analytic_germ_directional_nmod_morphism]:
    the actual fixed directional coefficient is an
    additive map, supporting finite sums in 3.4.8(5), p. 328. *)
Lemma analytic_germ_directional_nmod_morphism:nmod_morphism (fun alpha:G=>c alpha v).
Proof. split;[exact:analytic_germ_directional_zero|exact:analytic_germ_directional_add]. Qed.
(** Source for [analytic_germ_directional_sum]: actual
    finite germ sums have the corresponding coefficient
    sums, supporting 3.4.8(5), p. 328, from
    the derivative arithmetic in 3.4.5, p. 319. *)
Lemma analytic_germ_directional_sum (T:finType) (F:T->G):
  c (\sum_(i:T) F i) v = \sum_(i:T) c (F i) v.
Proof. exact:(big_morph (fun alpha:G=>c alpha v) analytic_germ_directional_add analytic_germ_directional_zero). Qed.
End Arithmetic.
