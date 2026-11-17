(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(2), p. 326:
    the original pointed coordinate pullback as a ring
    homomorphism. This hierarchy adapter uses only its
    independent representative laws and proved arithmetic. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicAtUP HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormAnalyticUP HolomorphicGermUP HolomorphicGermRing
  PointedHolomorphicPullbackUP PointedHolomorphicPullbackRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Morphism.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NY:Y->R).
Variable hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY.
Variable u:X->Y.
Variables (a:X) (b:Y).
Variable P:holomorphic_germ_space hNY b->holomorphic_germ_space hNX a.
Hypothesis hP:is_pointed_holomorphic_germ_pullback u P.
Local Notation GX:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)].
Local Notation GY:=[the comNzRingType of (@holomorphic_germ_ring R Y NY hNY b)].

(** Source for [pointed_pullback_ring_map]: the original
    map on analytic germs, viewed between their actual
    ring carriers, supporting 3.4.8(1),(2), p. 326. *)
Definition pointed_pullback_ring_map (alpha:GY):GX:=
  P alpha.

(** Source for [pointed_pullback_ring_map_additive]: zero
    and addition are preserved, supporting 3.4.8(1),(2), p. 326. *)
Lemma pointed_pullback_ring_map_additive:nmod_morphism pointed_pullback_ring_map.
Proof.
split.
- exact:(@pointed_holomorphic_pullback_constant R X Y NX NY hNX hNY a b u P hP 0).
- move=>alpha beta;exact:(@pointed_holomorphic_pullback_add R X Y NX NY hNX hNY a b u P hP alpha beta).
Qed.
HB.instance Definition _:=GRing.isNmodMorphism.Build GY GX
  pointed_pullback_ring_map pointed_pullback_ring_map_additive.

(** Source for [pointed_pullback_ring_map_multiplicative]:
    one and multiplication are preserved, supporting the
    original ring map in 3.4.8(1),(2), p. 326. *)
Lemma pointed_pullback_ring_map_multiplicative:monoid_morphism pointed_pullback_ring_map.
Proof.
split.
- exact:(@pointed_holomorphic_pullback_constant R X Y NX NY hNX hNY a b u P hP 1).
- move=>alpha beta;exact:(@pointed_holomorphic_pullback_multiply R X Y NX NY hNX hNY a b u P hP alpha beta).
Qed.
HB.instance Definition _:=GRing.isMonoidMorphism.Build GY GX
  pointed_pullback_ring_map pointed_pullback_ring_map_multiplicative.

(** Source for [pointed_holomorphic_germ_ring_pullback]: the
    original ring homomorphism on germ rings, with
    its proved hierarchy structure, 3.4.8(1),(2), p. 326.
    Its function is the existing opaque pullback. *)
Definition pointed_holomorphic_germ_ring_pullback:{rmorphism GY->GX}:=
  GRing.RMorphism.clone GY GX pointed_pullback_ring_map _.
End Morphism.
