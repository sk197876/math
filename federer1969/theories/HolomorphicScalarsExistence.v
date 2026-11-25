(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(8), pp. 326, 329:
    the actual constant germs give the original
    scalar homomorphism. Reuse the established germ
    arithmetic, including the constant-product theorem
    of the Weierstrass normalization proof. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP RealNormUP HolomorphicGermUP HolomorphicGermSealed HolomorphicGermRing HolomorphicGermRingLaws
  HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP HolomorphicScalarsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Constants.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable a:X.
Local Notation G:=(@holomorphic_germ_ring R X NX hNX a).

(** Source for [holomorphic_scalar_germ_function]: private
    actual representative for the original scalar
    identification, 3.4.8(1), p. 326. *)
Definition holomorphic_scalar_germ_function (c:ComplexScalars.C R):G:=
  holomorphic_germ (@holomorphic_constant_representative R X NX hNX a c).

(** Source for [holomorphic_scalar_germ_additive]: original
    zero and addition are preserved by the
    scalar identification, 3.4.8(1), p. 326. *)
Lemma holomorphic_scalar_germ_additive:nmod_morphism holomorphic_scalar_germ_function.
Proof.
split;first by [].
move=>c d;rewrite /holomorphic_scalar_germ_function.
change (holomorphic_germ (@holomorphic_constant_representative R X NX hNX a (c+d)) =
  @HolomorphicGerms.add R X NX hNX a
    (holomorphic_germ (@holomorphic_constant_representative R X NX hNX a c))
    (holomorphic_germ (@holomorphic_constant_representative R X NX hNX a d))).
rewrite (@holomorphic_germ_add_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
apply:holomorphic_germ_pointwise_equality=>x;by [].
Qed.
HB.instance Definition _:=GRing.isNmodMorphism.Build (ComplexScalars.C R) G holomorphic_scalar_germ_function holomorphic_scalar_germ_additive.

(** Source for [holomorphic_scalar_germ_multiplicative]: original
    scalar products retain the already proved
    constant-germ product formula, supporting
    3.4.8(1),(8), pp. 326, 329. *)
Lemma holomorphic_scalar_germ_multiplicative:monoid_morphism holomorphic_scalar_germ_function.
Proof.
split;first by [].
move=>c d;rewrite /holomorphic_scalar_germ_function.
change (holomorphic_germ (@holomorphic_constant_representative R X NX hNX a (c*d)) =
  @HolomorphicGerms.mul R X NX hNX a
    (holomorphic_germ (@holomorphic_constant_representative R X NX hNX a c))
    (holomorphic_germ (@holomorphic_constant_representative R X NX hNX a d))).
rewrite (@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
apply:holomorphic_germ_pointwise_equality=>x;reflexivity.
Qed.
HB.instance Definition _:=GRing.isMonoidMorphism.Build (ComplexScalars.C R) G holomorphic_scalar_germ_function holomorphic_scalar_germ_multiplicative.

(** Source for [holomorphic_scalar_map_exists]: the original
    constant identification exists as a ring
    homomorphism, 3.4.8(1),(8), pp. 326, 329. *)
Theorem holomorphic_scalar_map_exists:exists scalar:{rmorphism (ComplexScalars.C R)->G},is_holomorphic_scalar_map scalar.
Proof. exists (GRing.RMorphism.clone (ComplexScalars.C R) G holomorphic_scalar_germ_function _)=>c;by []. Qed.
End Constants.

(** Source for [holomorphic_scalar_map_unique]: every original
    scalar representative determines the same image,
    3.4.8(1), p. 326. *)
Lemma holomorphic_scalar_map_unique (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a
  (scalar other:{rmorphism (ComplexScalars.C R)->@holomorphic_germ_ring R X NX hNX a}):
  is_holomorphic_scalar_map scalar ->is_holomorphic_scalar_map other ->forall c,scalar c = other c.
Proof. move=>hScalar hOther c;by rewrite hScalar hOther. Qed.
