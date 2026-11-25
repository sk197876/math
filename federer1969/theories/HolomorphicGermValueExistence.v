(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: the actual
    germ value is a ring homomorphism. Local representative
    choice serves only to prove existence; centre equality
    makes the value independent of that choice. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP HolomorphicGermRepresentatives HolomorphicGermUP
  HolomorphicGermSealed HolomorphicGermRingLaws HolomorphicGermRing HolomorphicGermValueUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Existence.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable a:X.
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)].

(** Source for [holomorphic_germ_value_witness]: the value
    of a local representative is a private existence
    witness, supporting 3.4.7, p. 325. *)
Definition holomorphic_germ_value_witness (alpha:G):ComplexScalars.C R:=
  holomorphic_representative_value
    (projT1 (cid (@holomorphic_germ_has_representative R X NX hNX a alpha))) a.

(** Source for [holomorphic_germ_value_witness_representative]: every
    original representative gives the same centre value,
    supporting the independent laws in 3.4.7, p. 325. *)
Lemma holomorphic_germ_value_witness_representative (f:@holomorphic_representative_type R X NX hNX a):
  holomorphic_germ_value_witness (holomorphic_germ f) = holomorphic_representative_value f a.
Proof.
have hEqual:=projT2 (cid (@holomorphic_germ_has_representative R X NX hNX a (holomorphic_germ f))).
exact:(@holomorphic_germ_equal_at_centre R X NX hNX a _ f hEqual).
Qed.

(** Source for [holomorphic_germ_value_additive]: centre values
    preserve addition and zero, supporting the specialization
    in 3.4.7, p. 325. *)
Lemma holomorphic_germ_value_additive:nmod_morphism holomorphic_germ_value_witness.
Proof.
split.
- exact:(holomorphic_germ_value_witness_representative (@holomorphic_constant_representative R X NX hNX a 0)).
- move=>alpha beta.
  have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
  have [g hg]:=@holomorphic_germ_has_representative R X NX hNX a beta.
  rewrite -hf -hg.
  change (holomorphic_germ_value_witness (@HolomorphicGerms.add R X NX hNX a (holomorphic_germ f) (holomorphic_germ g)) =
    holomorphic_germ_value_witness (holomorphic_germ f)+holomorphic_germ_value_witness (holomorphic_germ g)).
  rewrite (@holomorphic_germ_add_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
  by rewrite !holomorphic_germ_value_witness_representative.
Qed.
#[local] HB.instance Definition _:=GRing.isNmodMorphism.Build G (ComplexScalars.C R)
  holomorphic_germ_value_witness holomorphic_germ_value_additive.

(** Source for [holomorphic_germ_value_multiplicative]: centre
    values preserve products and one, supporting units
    and specialization in 3.4.7, p. 325. *)
Lemma holomorphic_germ_value_multiplicative:monoid_morphism holomorphic_germ_value_witness.
Proof.
split.
- exact:(holomorphic_germ_value_witness_representative (@holomorphic_constant_representative R X NX hNX a 1)).
- move=>alpha beta.
  have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
  have [g hg]:=@holomorphic_germ_has_representative R X NX hNX a beta.
  rewrite -hf -hg.
  change (holomorphic_germ_value_witness (@HolomorphicGerms.mul R X NX hNX a (holomorphic_germ f) (holomorphic_germ g)) =
    holomorphic_germ_value_witness (holomorphic_germ f)*holomorphic_germ_value_witness (holomorphic_germ g)).
  rewrite (@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
  by rewrite !holomorphic_germ_value_witness_representative.
Qed.
#[local] HB.instance Definition _:=GRing.isMonoidMorphism.Build G (ComplexScalars.C R)
  holomorphic_germ_value_witness holomorphic_germ_value_multiplicative.

(** Source for [holomorphic_germ_value_exists]: an actual
    representative-independent centre-value homomorphism exists,
    supporting the original argument in 3.4.7, p. 325. *)
Theorem holomorphic_germ_value_exists:
  exists value:{rmorphism G->(ComplexScalars.C R)},is_holomorphic_germ_value_at_centre value.
Proof.
exists (GRing.RMorphism.clone G (ComplexScalars.C R) holomorphic_germ_value_witness _).
exact:holomorphic_germ_value_witness_representative.
Qed.
End Existence.
