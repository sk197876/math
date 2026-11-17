(** Federer (1969), 3.4.7, p. 325: the
    original analytic pullback is a ring homomorphism,
    making the ambient ring a transverse module.
    This hierarchy adapter uses only the proved opaque
    pullback and its public arithmetic laws. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormAnalyticUP AnalyticGermUP AnalyticGermRing
  AnalyticPullbackSealed AnalyticPullbackRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Morphism.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Variable hNX:is_real_norm NX.
Variable hNY:is_real_norm NY.
Variable A:set X.
Variable u:X->Y.
Variable a:X.
Variable hu:@norm_analytic_at R X Y NX NY hNX hNY A u a.
Local Notation GX:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
Local Notation GY:=[the comNzRingType of (@analytic_germ_ring R Y NY hNY (u a))].

(** Source for [analytic_pullback_ring_map]: the original
    map on analytic germs, viewed between their actual
    ring carriers, supporting 3.4.7, p. 325. *)
Definition analytic_pullback_ring_map (alpha:GY):GX:=
  @AnalyticPullback.map R X Y NX NY hNX hNY A u a hu alpha.

(** Source for [analytic_pullback_ring_map_additive]: zero
    and addition are preserved, supporting 3.4.7, p. 325. *)
Lemma analytic_pullback_ring_map_additive:nmod_morphism analytic_pullback_ring_map.
Proof.
split.
- exact:(@analytic_germ_pullback_zero R X Y NX NY hNX hNY A u a hu).
- move=>alpha beta;exact:(@analytic_germ_pullback_add R X Y NX NY hNX hNY A u a hu alpha beta).
Qed.
HB.instance Definition _:=GRing.isNmodMorphism.Build GY GX
  analytic_pullback_ring_map analytic_pullback_ring_map_additive.

(** Source for [analytic_pullback_ring_map_multiplicative]:
    one and multiplication are preserved, supporting the
    original ring map in 3.4.7, p. 325. *)
Lemma analytic_pullback_ring_map_multiplicative:monoid_morphism analytic_pullback_ring_map.
Proof.
split.
- exact:(@analytic_germ_pullback_one R X Y NX NY hNX hNY A u a hu).
- move=>alpha beta;exact:(@analytic_germ_pullback_multiply R X Y NX NY hNX hNY A u a hu alpha beta).
Qed.
HB.instance Definition _:=GRing.isMonoidMorphism.Build GY GX
  analytic_pullback_ring_map analytic_pullback_ring_map_multiplicative.

(** Source for [analytic_germ_ring_pullback]: the
    original ring homomorphism on germ rings, with
    its proved hierarchy structure, 3.4.7, p. 325.
    Its function is the existing opaque pullback. *)
Definition analytic_germ_ring_pullback:{rmorphism GY->GX}:=
  GRing.RMorphism.clone GY GX analytic_pullback_ring_map _.
End Morphism.
