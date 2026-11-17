(** Federer (1969), 3.4.7, p. 325: the private
    fraction construction proves the independently specified
    field-of-fractions laws. No factorization theorem is imported. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg boolp generic_quotient ring.
From Federer Require Import CommutativeDomainUP FractionFieldUP FractionPairEquivalence
  FractionPairOperations FractionQuotient FractionRingConstruction FractionFieldConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Existence.
Variable A:comNzRingType.
Hypothesis hDomain:is_commutative_integral_domain A.
Local Notation K:=(@FractionFieldWitness.field_type A hDomain).
Local Notation project:=(@fraction_quotient_projection A hDomain).

(** Source for [fraction_field_embedding_map]: actual constants
    in the private fraction field, supporting 3.4.7, p. 325. *)
Definition fraction_field_embedding_map (a:A):K:=@fraction_quotient_constant A hDomain a.

(** Source for [fraction_field_embedding_additive]: the original
    constants preserve addition and zero, supporting 3.4.7, p. 325. *)
Lemma fraction_field_embedding_additive:nmod_morphism fraction_field_embedding_map.
Proof.
split;first by [].
move=>a b.
change (project (fraction_pair_constant (a+b)) =
  @fraction_quotient_add A hDomain (project (fraction_pair_constant a)) (project (fraction_pair_constant b))).
rewrite fraction_quotient_add_projection;apply/fraction_quotient_equality/eqP.
rewrite /fraction_pair_relation /fraction_pair_add /fraction_pair_constant /=;ring.
Qed.
HB.instance Definition _:=GRing.isNmodMorphism.Build A K
  fraction_field_embedding_map fraction_field_embedding_additive.

(** Source for [fraction_field_embedding_multiplicative]: original
    constants preserve products and one, supporting 3.4.7, p. 325. *)
Lemma fraction_field_embedding_multiplicative:monoid_morphism fraction_field_embedding_map.
Proof.
split;first by [].
move=>a b.
change (project (fraction_pair_constant (a*b)) =
  @fraction_quotient_multiply A hDomain (project (fraction_pair_constant a)) (project (fraction_pair_constant b))).
rewrite fraction_quotient_multiply_projection;apply/fraction_quotient_equality/eqP.
rewrite /fraction_pair_relation /fraction_pair_multiply /fraction_pair_constant /=;ring.
Qed.
HB.instance Definition _:=GRing.isMonoidMorphism.Build A K
  fraction_field_embedding_map fraction_field_embedding_multiplicative.

(** Source for [fraction_field_embedding]: the actual ring
    homomorphism from original coefficients into their fraction
    field, supporting 3.4.7, p. 325. *)
Definition fraction_field_embedding:{rmorphism A->K}:=
  GRing.RMorphism.clone A K fraction_field_embedding_map _.

(** Source for [fraction_field_embedding_faithful]: equality of
    constant fractions is equality of original coefficients,
    supporting 3.4.7, p. 325. *)
Lemma fraction_field_embedding_faithful:injective fraction_field_embedding.
Proof.
move=>a b h.
have hRel:=(@fraction_quotient_equality A hDomain
  (fraction_pair_constant a) (fraction_pair_constant b)).1 h.
move/eqP:hRel;by rewrite /fraction_pair_relation /fraction_pair_constant /= !mulr1.
Qed.

(** Source for [fraction_field_representation]: every actual
    field element is a fraction of original coefficients
    with a nonzero denominator, supporting 3.4.7, p. 325. *)
Lemma fraction_field_representation (x:K):exists a b:A,
  b<>0 /\x = fraction_field_embedding a/fraction_field_embedding b.
Proof.
pose p:=repr x.
have hDen:(val p).2<>0 by apply/eqP;exact:valP p.
have hEmbeddedDen:fraction_field_embedding (val p).2!=0.
  apply/eqP=>h;apply:hDen;apply:fraction_field_embedding_faithful.
  by rewrite rmorph0.
exists (val p).1,(val p).2;split;first exact:hDen.
apply:(mulIf hEmbeddedDen);rewrite divfK //.
change (@fraction_quotient_multiply A hDomain x (project (fraction_pair_constant (val p).2)) =
  project (fraction_pair_constant (val p).1)).
rewrite -[x]fraction_quotient_repr fraction_quotient_multiply_projection.
apply/fraction_quotient_equality/eqP.
rewrite /fraction_pair_relation /fraction_pair_multiply /fraction_pair_constant /p /=;ring.
Qed.

(** Source for [fraction_field_witness_laws]: the private
    witness satisfies the independent fraction laws for
    the Gauss argument in 3.4.7, p. 325. *)
Lemma fraction_field_witness_laws:is_commutative_fraction_field fraction_field_embedding.
Proof. constructor;[exact:fraction_field_embedding_faithful|exact:fraction_field_representation]. Qed.
End Existence.

(** Source for [commutative_fraction_field_exists]: every original
    integral domain has a fraction field with the
    stated independent laws, supporting 3.4.7, p. 325. *)
Theorem commutative_fraction_field_exists (A:comNzRingType)
    (hDomain:is_commutative_integral_domain A):
  exists (K:fieldType) (embed:{rmorphism A->K}),is_commutative_fraction_field embed.
Proof.
exists (@FractionFieldWitness.field_type A hDomain),(@fraction_field_embedding A hDomain).
exact:fraction_field_witness_laws.
Qed.
