(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(2), p. 326:
    pointed coordinate pullbacks preserve the actual ring
    operations. The independent representative laws prove
    these identities before a hierarchy adapter is constructed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicAtUP HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP HolomorphicGermRepresentatives HolomorphicGermUP
  HolomorphicGermSealed HolomorphicGermRingLaws HolomorphicGermRing PointedHolomorphicPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section RingLaws.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NY:Y->R).
Variables (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY).
Variables (a:X) (b:Y) (u:X->Y).
Variable P:holomorphic_germ_space hNY b->holomorphic_germ_space hNX a.
Hypothesis hP:is_pointed_holomorphic_germ_pullback u P.
Local Notation GY:=[the comNzRingType of (@holomorphic_germ_ring R Y NY hNY b)].
Local Notation GX:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)].

(** Source for [pointed_holomorphic_pullback_add]: the original
    coordinate pullback preserves addition, supporting
    3.4.8(1),(2), p. 326. *)
Lemma pointed_holomorphic_pullback_add (alpha beta:GY):
  P (alpha+beta)=(P alpha:GX)+(P beta:GX).
Proof.
have [f <-]:=@holomorphic_germ_has_representative R Y NY hNY b alpha.
have [g <-]:=@holomorphic_germ_has_representative R Y NY hNY b beta.
have [pf [hPF hVF]]:=hP f;have [pg [hPG hVG]]:=hP g.
have [ps [hPS hVS]]:=hP (@holomorphic_add_representatives R Y NY hNY b f g).
change (P (@HolomorphicGerms.add R Y NY hNY b (holomorphic_germ f) (holomorphic_germ g))=
  @HolomorphicGerms.add R X NX hNX a (P (holomorphic_germ f)) (P (holomorphic_germ g))).
rewrite (@holomorphic_germ_add_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R Y NY hNY b))
  hPS hPF hPG (@holomorphic_germ_add_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
apply:holomorphic_germ_pointwise_equality=>x.
change (holomorphic_representative_value ps x=holomorphic_representative_value pf x+holomorphic_representative_value pg x).
by rewrite hVS hVF hVG.
Qed.

(** Source for [pointed_holomorphic_pullback_multiply]: the original
    coordinate pullback preserves multiplication, supporting
    3.4.8(1),(2), p. 326. *)
Lemma pointed_holomorphic_pullback_multiply (alpha beta:GY):
  P (alpha*beta)=(P alpha:GX)*(P beta:GX).
Proof.
have [f <-]:=@holomorphic_germ_has_representative R Y NY hNY b alpha.
have [g <-]:=@holomorphic_germ_has_representative R Y NY hNY b beta.
have [pf [hPF hVF]]:=hP f;have [pg [hPG hVG]]:=hP g.
have [ps [hPS hVS]]:=hP (@holomorphic_multiply_representatives R Y NY hNY b f g).
change (P (@HolomorphicGerms.mul R Y NY hNY b (holomorphic_germ f) (holomorphic_germ g))=
  @HolomorphicGerms.mul R X NX hNX a (P (holomorphic_germ f)) (P (holomorphic_germ g))).
rewrite (@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R Y NY hNY b))
  hPS hPF hPG (@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
apply:holomorphic_germ_pointwise_equality=>x.
change (holomorphic_representative_value ps x=holomorphic_representative_value pf x*holomorphic_representative_value pg x).
by rewrite hVS hVF hVG.
Qed.

(** Source for [pointed_holomorphic_pullback_constant]: the original
    coordinate pullback preserves scalar constants, including
    zero and one, supporting 3.4.8(1),(2), p. 326. *)
Lemma pointed_holomorphic_pullback_constant (c:ComplexScalars.C R):
  P (holomorphic_germ (@holomorphic_constant_representative R Y NY hNY b c))=
    holomorphic_germ (@holomorphic_constant_representative R X NX hNX a c).
Proof.
have [g [hG hValues]]:=hP (@holomorphic_constant_representative R Y NY hNY b c).
rewrite hG;apply:holomorphic_germ_pointwise_equality=>x.
exact:hValues x.
Qed.
End RingLaws.
