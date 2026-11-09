(** Federer (1969), 3.4.5, p. 319: the original
    analytic pullback preserves the ring operations and its unit.
    Every proof uses the public representative equations only. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormAnalyticUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermSealed AnalyticGermRingLaws AnalyticGermRing
  AnalyticPullbackRepresentative AnalyticPullbackUP AnalyticPullbackSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RingLaws.
Variable R:realType.
Variables X Y:lmodType R.
Variable NX:X->R.
Variable NY:Y->R.
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable A:set X.
Variable u:X->Y.
Variable a:X.
Hypothesis hu:@norm_analytic_at R X Y NX NY hNX hNY A u a.
Local Notation P:=(@AnalyticPullback.map R X Y NX NY hNX hNY A u a hu).
Local Notation GY:=[the comNzRingType of (@analytic_germ_ring R Y NY hNY (u a))].
Local Notation GX:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].

(** Source for [analytic_germ_pullback_add]: the additive
    homomorphism law of 3.4.5, p. 319. *)
Lemma analytic_germ_pullback_add (alpha beta:GY):P (alpha+beta)=(P alpha:GX)+(P beta:GX).
Proof.
have [f <-]:=@analytic_germ_has_representative R Y NY hNY (u a) alpha.
have [g <-]:=@analytic_germ_has_representative R Y NY hNY (u a) beta.
change (P (@AnalyticGerms.add R Y NY hNY (u a) (analytic_germ f) (analytic_germ g))=
  @AnalyticGerms.add R X NX hNX a (P (analytic_germ f)) (P (analytic_germ g))).
rewrite (@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R Y NY hNY (u a)))
  !(@AnalyticPullback.laws R X Y NX NY hNX hNY A u a hu)
  (@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
apply:analytic_germ_pointwise_equality=>x;reflexivity.
Qed.

(** Source for [analytic_germ_pullback_multiply]: the
    multiplication homomorphism law of 3.4.5, p. 319. *)
Lemma analytic_germ_pullback_multiply (alpha beta:GY):P (alpha*beta)=(P alpha:GX)*(P beta:GX).
Proof.
have [f <-]:=@analytic_germ_has_representative R Y NY hNY (u a) alpha.
have [g <-]:=@analytic_germ_has_representative R Y NY hNY (u a) beta.
change (P (@AnalyticGerms.mul R Y NY hNY (u a) (analytic_germ f) (analytic_germ g))=
  @AnalyticGerms.mul R X NX hNX a (P (analytic_germ f)) (P (analytic_germ g))).
rewrite (@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R Y NY hNY (u a)))
  !(@AnalyticPullback.laws R X Y NX NY hNX hNY A u a hu)
  (@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
apply:analytic_germ_pointwise_equality=>x;reflexivity.
Qed.

(** Source for [analytic_germ_pullback_constant]: every
    scalar constant pulls back to itself; this includes the
    zero and unit laws of 3.4.5, p. 319. *)
Lemma analytic_germ_pullback_constant (c:R):
  P (analytic_germ (@analytic_constant_representative R Y NY hNY (u a) c))=
  analytic_germ (@analytic_constant_representative R X NX hNX a c).
Proof.
rewrite (@AnalyticPullback.laws R X Y NX NY hNX hNY A u a hu).
apply:analytic_germ_pointwise_equality=>x;reflexivity.
Qed.

(** Source for [analytic_germ_pullback_one]: the unit law
    in the original ring homomorphism, 3.4.5, p. 319. *)
Lemma analytic_germ_pullback_one:P (1:GY)=(1:GX).
Proof. exact:(analytic_germ_pullback_constant 1). Qed.

(** Source for [analytic_germ_pullback_zero]: the zero law
    in the original ring homomorphism, 3.4.5, p. 319. *)
Lemma analytic_germ_pullback_zero:P (0:GY)=(0:GX).
Proof. exact:(analytic_germ_pullback_constant 0). Qed.

(** Source for [analytic_germ_pullback_difference]: actual
    subtraction is preserved, supporting continuity of the original
    homomorphism of 3.4.5, p. 319. *)
Lemma analytic_germ_pullback_difference (alpha beta:GY):P (alpha-beta)=(P alpha:GX)-(P beta:GX).
Proof.
have hEq:=analytic_germ_pullback_add (alpha-beta) beta.
rewrite subrK in hEq.
apply:(@addIr GX (P beta));by rewrite subrK -hEq.
Qed.
End RingLaws.
