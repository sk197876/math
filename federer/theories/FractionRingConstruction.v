(** Federer (1969), 3.4.7, p. 325: the fraction
    quotient carries its proved ring operations. This private
    existence witness will be hidden by the fraction-field seal. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg boolp generic_quotient ring.
From Federer Require Import CommutativeDomainUP FractionPairEquivalence FractionPairOperations FractionQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Ring.
Variable A:comNzRingType.
Hypothesis hDomain:is_commutative_integral_domain A.
Local Notation K:=(@fraction_quotient_carrier A hDomain).
Local Notation project:=(@fraction_quotient_projection A hDomain).
Local Notation constant:=(@fraction_quotient_constant A hDomain).
Local Notation add:=(@fraction_quotient_add A hDomain).
Local Notation opp:=(@fraction_quotient_opp A hDomain).
Local Notation mul:=(@fraction_quotient_multiply A hDomain).

(** Source for [fraction_ring_add_associative]: associativity
    of fraction addition, supporting 3.4.7, p. 325. *)
Lemma fraction_ring_add_associative:associative add.
Proof.
move=>x y z;rewrite -[x]fraction_quotient_repr -[y]fraction_quotient_repr -[z]fraction_quotient_repr.
rewrite !fraction_quotient_add_projection;apply/fraction_quotient_equality/eqP.
rewrite /fraction_pair_relation /fraction_pair_add /=;ring.
Qed.

(** Source for [fraction_ring_add_commutative]: commutativity
    of fraction addition, supporting 3.4.7, p. 325. *)
Lemma fraction_ring_add_commutative:commutative add.
Proof.
move=>x y;rewrite -[x]fraction_quotient_repr -[y]fraction_quotient_repr.
rewrite !fraction_quotient_add_projection;apply/fraction_quotient_equality/eqP.
rewrite /fraction_pair_relation /fraction_pair_add /=;ring.
Qed.

(** Source for [fraction_ring_add_zero]: zero is the
    additive unit, supporting 3.4.7, p. 325. *)
Lemma fraction_ring_add_zero:left_id (constant 0) add.
Proof.
move=>x;rewrite -[x]fraction_quotient_repr /fraction_quotient_constant fraction_quotient_add_projection.
apply/fraction_quotient_equality/eqP.
rewrite /fraction_pair_relation /fraction_pair_add /fraction_pair_constant /=;ring.
Qed.

(** Source for [fraction_ring_add_negate]: fraction negatives
    give additive inverses, supporting 3.4.7, p. 325. *)
Lemma fraction_ring_add_negate:left_inverse (constant 0) opp add.
Proof.
move=>x;rewrite -[x]fraction_quotient_repr fraction_quotient_opp_projection
  fraction_quotient_add_projection /fraction_quotient_constant.
apply/fraction_quotient_equality/eqP.
rewrite /fraction_pair_relation /fraction_pair_add /fraction_pair_opp /fraction_pair_constant /=;ring.
Qed.
HB.instance Definition _:=GRing.isZmodule.Build K
  fraction_ring_add_associative fraction_ring_add_commutative
  fraction_ring_add_zero fraction_ring_add_negate.

(** Source for [fraction_ring_multiply_associative]: fraction
    multiplication is associative, supporting 3.4.7, p. 325. *)
Lemma fraction_ring_multiply_associative:associative mul.
Proof.
move=>x y z;rewrite -[x]fraction_quotient_repr -[y]fraction_quotient_repr -[z]fraction_quotient_repr.
rewrite !fraction_quotient_multiply_projection;apply/fraction_quotient_equality/eqP.
rewrite /fraction_pair_relation /fraction_pair_multiply /=;ring.
Qed.

(** Source for [fraction_ring_multiply_commutative]: fraction
    multiplication is commutative, supporting 3.4.7, p. 325. *)
Lemma fraction_ring_multiply_commutative:commutative mul.
Proof.
move=>x y;rewrite -[x]fraction_quotient_repr -[y]fraction_quotient_repr.
rewrite !fraction_quotient_multiply_projection;apply/fraction_quotient_equality/eqP.
rewrite /fraction_pair_relation /fraction_pair_multiply /=;ring.
Qed.

(** Source for [fraction_ring_multiply_one]: one is the
    multiplicative unit, supporting 3.4.7, p. 325. *)
Lemma fraction_ring_multiply_one:left_id (constant 1) mul.
Proof.
move=>x;rewrite -[x]fraction_quotient_repr /fraction_quotient_constant fraction_quotient_multiply_projection.
apply/fraction_quotient_equality/eqP.
rewrite /fraction_pair_relation /fraction_pair_multiply /fraction_pair_constant /=;ring.
Qed.

(** Source for [fraction_ring_distributive]: multiplication
    distributes over addition, supporting 3.4.7, p. 325. *)
Lemma fraction_ring_distributive:left_distributive mul add.
Proof.
move=>x y z.
rewrite -[x]fraction_quotient_repr -[y]fraction_quotient_repr -[z]fraction_quotient_repr.
rewrite (@fraction_quotient_add_projection A hDomain (repr x) (repr y)).
rewrite (@fraction_quotient_multiply_projection A hDomain (repr x) (repr z)).
rewrite (@fraction_quotient_multiply_projection A hDomain (repr y) (repr z)).
rewrite fraction_quotient_multiply_projection fraction_quotient_add_projection.
apply/fraction_quotient_equality/eqP.
rewrite /fraction_pair_relation /fraction_pair_add /fraction_pair_multiply /=;ring.
Qed.

(** Source for [fraction_ring_one_nonzero]: the original
    distinct constants remain distinct in the quotient,
    supporting 3.4.7, p. 325. *)
Lemma fraction_ring_one_nonzero:constant 1 != 0.
Proof.
apply/eqP=>h;have hRelation:=(@fraction_quotient_equality A hDomain
  (fraction_pair_constant 1) (fraction_pair_constant 0)).1 h.
move/eqP:hRelation;rewrite /fraction_pair_constant /= mulr1 mul0r.
by move=>hOne;move:(oner_neq0 A);rewrite hOne eqxx.
Qed.
HB.instance Definition _:=@GRing.Zmodule_isComNzRing.Build K (constant 1) mul
  fraction_ring_multiply_associative fraction_ring_multiply_commutative
  fraction_ring_multiply_one fraction_ring_distributive fraction_ring_one_nonzero.
End Ring.
