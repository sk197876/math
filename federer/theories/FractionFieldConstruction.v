(** Federer (1969), 3.4.7, p. 325: the actual
    fraction ring is a field. Inverses are proved
    to exist before an operation is selected. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg boolp generic_quotient ring.
From Federer Require Import CommutativeDomainUP FractionPairEquivalence FractionPairOperations
  FractionQuotient FractionRingConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Module FractionFieldWitness.
Section Field.
Variable A:comNzRingType.
Hypothesis hDomain:is_commutative_integral_domain A.
(** Source for [fraction_field_carrier]: a distinct hierarchy
    carrier for the private field witness supporting 3.4.7,
    p. 325. It inherits only the proved fraction-ring laws. *)
Definition fraction_field_carrier:Type:=@fraction_quotient_carrier A hDomain.
#[local] HB.instance Definition _:=Choice.copy fraction_field_carrier
  [the choiceType of (@fraction_quotient_carrier A hDomain)].
#[local] HB.instance Definition _:=GRing.ComNzRing.copy fraction_field_carrier
  [the comNzRingType of (@fraction_quotient_carrier A hDomain)].
Local Notation K:=[the comNzRingType of fraction_field_carrier].
Local Notation project:=(@fraction_quotient_projection A hDomain).

(** Source for [fraction_nonzero_numerator]: a nonzero
    fraction class has a nonzero representative numerator,
    supporting the field witness for 3.4.7, p. 325. *)
Lemma fraction_nonzero_numerator (x:K):x!=0 ->(val (repr x)).1!=0.
Proof.
move=>hx;apply/eqP=>hNum.
have hZero:x = 0.
  rewrite -[x]fraction_quotient_repr.
  change (project (repr x) = project (fraction_pair_constant 0)).
  apply/fraction_quotient_equality/eqP.
  by rewrite /fraction_pair_relation /fraction_pair_constant /= hNum !mul0r.
by move:hx;rewrite hZero eqxx.
Qed.

(** Source for [fraction_nonzero_inverse_exists]: interchanging
    the numerator and denominator gives an actual inverse
    of every nonzero fraction, supporting 3.4.7, p. 325. *)
Lemma fraction_nonzero_inverse_exists (x:K):x!=0 ->exists y:K,y*x = 1.
Proof.
move=>hx.
pose p:=repr x.
have hNum:(val p).1!=0:=fraction_nonzero_numerator hx.
pose q:@nonzero_denominator_pair A:=Sub ((val p).2,(val p).1) hNum.
exists (project q).
change (@fraction_quotient_multiply A hDomain (project q) x =
  project (fraction_pair_constant 1)).
rewrite -[x]fraction_quotient_repr fraction_quotient_multiply_projection.
apply/fraction_quotient_equality/eqP.
rewrite /fraction_pair_relation /fraction_pair_multiply /fraction_pair_constant /q /p /=;ring.
Qed.

(** Source for [fraction_inverse_operation_exists]: an inverse
    exists with zero mapped to zero, supporting the
    field witness in 3.4.7, p. 325. *)
Lemma fraction_inverse_operation_exists (x:K):
  exists y:K,(x = 0 ->y = 0) /\(x!=0 ->y*x = 1).
Proof.
case:(eqVneq x 0)=>[hZero|hNonzero].
- exists 0;split;first by [].
  by rewrite hZero.
- have [y hy]:=fraction_nonzero_inverse_exists hNonzero.
  exists y;split;last by [].
  move=>h;by move:hNonzero;rewrite h eqxx.
Qed.

(** Source for [fraction_inverse_witness]: a private choice
    from proved inverse existence, supporting 3.4.7, p. 325. *)
Definition fraction_inverse_witness (x:K):K:=
  projT1 (cid (fraction_inverse_operation_exists x)).

(** Source for [fraction_inverse_multiply]: the selected
    inverse satisfies its original product equation,
    supporting 3.4.7, p. 325. *)
Lemma fraction_inverse_multiply (x:K):x!=0 ->fraction_inverse_witness x*x = 1.
Proof. exact:(projT2 (cid (fraction_inverse_operation_exists x))).2. Qed.

(** Source for [fraction_inverse_zero]: the selected inverse
    maps zero to zero, supporting 3.4.7, p. 325. *)
Lemma fraction_inverse_zero:fraction_inverse_witness 0 = 0.
Proof. exact:((projT2 (cid (fraction_inverse_operation_exists 0))).1 erefl). Qed.
(* The chosen inverse supplies additional hierarchy data.
   Keep this instance local to the private construction module;
   only the packed field witness is exposed to the existence proof. *)
#[local] HB.instance Definition _:=GRing.ComNzRing_isField.Build fraction_field_carrier
  fraction_inverse_multiply fraction_inverse_zero.

(** Source for [field_type]: the packed private fraction
    field witness, supporting existence for 3.4.7, p. 325.
    Its local hierarchy instance is not exported. *)
Definition field_type:fieldType:=[the fieldType of fraction_field_carrier].
End Field.
End FractionFieldWitness.
