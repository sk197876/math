(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: the original
    analytic pullback preserves the ring operations and its unit.
    Every proof uses the public representative equations only. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives RealNormUP HolomorphicAtUP HolomorphicGermRepresentatives HolomorphicGermOperationsUP HolomorphicGermUP
  HolomorphicGermSealed HolomorphicGermRingLaws HolomorphicGermRing
  HolomorphicPullbackRepresentative HolomorphicPullbackUP HolomorphicPullbackSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RingLaws.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable NY:Y->R.
Hypothesis hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Hypothesis hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY.
Variable A:set X.
Variable u:X->Y.
Variable a:X.
Hypothesis hu:@is_holomorphic_at R X Y NX NY hNX hNY A u a.
Local Notation P:=(@HolomorphicPullback.map R X Y NX NY hNX hNY A u a hu).
Local Notation GY:=[the comNzRingType of (@holomorphic_germ_ring R Y NY hNY (u a))].
Local Notation GX:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)].

(** Source for [holomorphic_germ_pullback_add]: the additive
    homomorphism law of 3.4.5, p. 319. *)
Lemma holomorphic_germ_pullback_add (alpha beta:GY):P (alpha+beta)=(P alpha:GX)+(P beta:GX).
Proof.
have [f <-]:=@holomorphic_germ_has_representative R Y NY hNY (u a) alpha.
have [g <-]:=@holomorphic_germ_has_representative R Y NY hNY (u a) beta.
change (P (@HolomorphicGerms.add R Y NY hNY (u a) (holomorphic_germ f) (holomorphic_germ g))=
  @HolomorphicGerms.add R X NX hNX a (P (holomorphic_germ f)) (P (holomorphic_germ g))).
rewrite (@holomorphic_germ_add_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R Y NY hNY (u a)))
  !(@HolomorphicPullback.laws R X Y NX NY hNX hNY A u a hu)
  (@holomorphic_germ_add_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
apply:holomorphic_germ_pointwise_equality=>x;reflexivity.
Qed.

(** Source for [holomorphic_germ_pullback_multiply]: the
    multiplication homomorphism law of 3.4.5, p. 319. *)
Lemma holomorphic_germ_pullback_multiply (alpha beta:GY):P (alpha*beta)=(P alpha:GX)*(P beta:GX).
Proof.
have [f <-]:=@holomorphic_germ_has_representative R Y NY hNY (u a) alpha.
have [g <-]:=@holomorphic_germ_has_representative R Y NY hNY (u a) beta.
change (P (@HolomorphicGerms.mul R Y NY hNY (u a) (holomorphic_germ f) (holomorphic_germ g))=
  @HolomorphicGerms.mul R X NX hNX a (P (holomorphic_germ f)) (P (holomorphic_germ g))).
rewrite (@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R Y NY hNY (u a)))
  !(@HolomorphicPullback.laws R X Y NX NY hNX hNY A u a hu)
  (@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
apply:holomorphic_germ_pointwise_equality=>x;reflexivity.
Qed.

(** Source for [holomorphic_germ_pullback_constant]: every
    scalar constant pulls back to itself; this includes the
    zero and unit laws of 3.4.5, p. 319. *)
Lemma holomorphic_germ_pullback_constant (c:ComplexScalars.C R):
  P (holomorphic_germ (@holomorphic_constant_representative R Y NY hNY (u a) c))=
  holomorphic_germ (@holomorphic_constant_representative R X NX hNX a c).
Proof.
rewrite (@HolomorphicPullback.laws R X Y NX NY hNX hNY A u a hu).
apply:holomorphic_germ_pointwise_equality=>x;reflexivity.
Qed.

(** Source for [holomorphic_germ_pullback_one]: the unit law
    in the original ring homomorphism, 3.4.5, p. 319. *)
Lemma holomorphic_germ_pullback_one:P (1:GY)=(1:GX).
Proof. exact:(holomorphic_germ_pullback_constant 1). Qed.

(** Source for [holomorphic_germ_pullback_zero]: the zero law
    in the original ring homomorphism, 3.4.5, p. 319. *)
Lemma holomorphic_germ_pullback_zero:P (0:GY)=(0:GX).
Proof. exact:(holomorphic_germ_pullback_constant 0). Qed.

(** Source for [holomorphic_germ_pullback_difference]: actual
    subtraction is preserved, supporting continuity of the original
    homomorphism of 3.4.5, p. 319. *)
Lemma holomorphic_germ_pullback_difference (alpha beta:GY):P (alpha-beta)=(P alpha:GX)-(P beta:GX).
Proof.
have hEq:=holomorphic_germ_pullback_add (alpha-beta) beta.
rewrite subrK in hEq.
apply:(@addIr GX (P beta));by rewrite subrK -hEq.
Qed.
End RingLaws.
