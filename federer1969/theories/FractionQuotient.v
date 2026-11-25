(** Federer (1969), 3.4.7, p. 325: a private quotient
    witness for the coefficient fraction field used by Gauss's
    lemma. The only imported quotient is the background set quotient. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg boolp generic_quotient.
From Federer Require Import CommutativeDomainUP FractionPairEquivalence FractionPairOperations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.
Section Quotient.
Variable A:comNzRingType.
Hypothesis hDomain:is_commutative_integral_domain A.
Local Notation P:=(@nonzero_denominator_pair A).
Canonical fraction_pair_equivalence:=EquivRel (@fraction_pair_relation A)
  (@fraction_pair_relation_refl A) (@fraction_pair_relation_sym A)
  (@fraction_pair_relation_trans A hDomain).

(** Source for [fraction_quotient_carrier]: equivalence classes
    of actual fractions, supporting 3.4.7, p. 325. *)
Definition fraction_quotient_carrier:={eq_quot (@fraction_pair_relation A)}.
HB.instance Definition _:=Choice.copy fraction_quotient_carrier {eq_quot (@fraction_pair_relation A)}.

(** Source for [fraction_quotient_projection]: representative
    to fraction-class projection, supporting 3.4.7, p. 325. *)
Definition fraction_quotient_projection (p:P):fraction_quotient_carrier:=\pi_fraction_quotient_carrier p.

(** Source for [fraction_quotient_equality]: equality is exactly
    cross multiplication, supporting 3.4.7, p. 325. *)
Lemma fraction_quotient_equality (p q:P):
  fraction_quotient_projection p = fraction_quotient_projection q <->fraction_pair_relation p q.
Proof. split=>h;[apply/(eqmodP fraction_pair_equivalence)|apply/(eqmodP fraction_pair_equivalence)];exact:h. Qed.

(** Source for [fraction_quotient_repr]: every class has an
    actual fraction representative, supporting 3.4.7, p. 325. *)
Lemma fraction_quotient_repr (x:fraction_quotient_carrier):
  fraction_quotient_projection (repr x) = x.
Proof. exact:reprK. Qed.

(** Source for [fraction_quotient_add_compatible]: sum classes
    are independent of representatives, supporting 3.4.7, p. 325. *)
Lemma fraction_quotient_add_compatible (p q r s:P):
  fraction_quotient_projection p = fraction_quotient_projection r ->
  fraction_quotient_projection q = fraction_quotient_projection s ->
  fraction_quotient_projection (fraction_pair_add hDomain p q) =
    fraction_quotient_projection (fraction_pair_add hDomain r s).
Proof.
move/fraction_quotient_equality=>hp;move/fraction_quotient_equality=>hq.
apply/fraction_quotient_equality;exact:fraction_pair_add_compatible hp hq.
Qed.

(** Source for [fraction_quotient_opp_compatible]: negative
    classes are well defined, supporting 3.4.7, p. 325. *)
Lemma fraction_quotient_opp_compatible (p q:P):
  fraction_quotient_projection p = fraction_quotient_projection q ->
  fraction_quotient_projection (fraction_pair_opp p) = fraction_quotient_projection (fraction_pair_opp q).
Proof. move/fraction_quotient_equality=>h;apply/fraction_quotient_equality;exact:fraction_pair_opp_compatible h. Qed.

(** Source for [fraction_quotient_multiply_compatible]: product
    classes are well defined, supporting 3.4.7, p. 325. *)
Lemma fraction_quotient_multiply_compatible (p q r s:P):
  fraction_quotient_projection p = fraction_quotient_projection r ->
  fraction_quotient_projection q = fraction_quotient_projection s ->
  fraction_quotient_projection (fraction_pair_multiply hDomain p q) =
    fraction_quotient_projection (fraction_pair_multiply hDomain r s).
Proof.
move/fraction_quotient_equality=>hp;move/fraction_quotient_equality=>hq.
apply/fraction_quotient_equality;exact:fraction_pair_multiply_compatible hp hq.
Qed.

(** Source for [fraction_quotient_constant]: original scalars
    as fraction classes, supporting 3.4.7, p. 325. *)
Definition fraction_quotient_constant (a:A):fraction_quotient_carrier:=
  fraction_quotient_projection (fraction_pair_constant a).

(** Source for [fraction_quotient_add]: actual addition on
    fraction classes, supporting 3.4.7, p. 325. *)
Definition fraction_quotient_add (x y:fraction_quotient_carrier):fraction_quotient_carrier:=
  fraction_quotient_projection (fraction_pair_add hDomain (repr x) (repr y)).

(** Source for [fraction_quotient_opp]: actual negation on
    fraction classes, supporting 3.4.7, p. 325. *)
Definition fraction_quotient_opp (x:fraction_quotient_carrier):fraction_quotient_carrier:=
  fraction_quotient_projection (fraction_pair_opp (repr x)).

(** Source for [fraction_quotient_multiply]: actual multiplication
    on fraction classes, supporting 3.4.7, p. 325. *)
Definition fraction_quotient_multiply (x y:fraction_quotient_carrier):fraction_quotient_carrier:=
  fraction_quotient_projection (fraction_pair_multiply hDomain (repr x) (repr y)).

(** Source for [fraction_quotient_add_projection]: addition
    has the original fraction formula, supporting 3.4.7, p. 325. *)
Lemma fraction_quotient_add_projection (p q:P):
  fraction_quotient_add (fraction_quotient_projection p) (fraction_quotient_projection q) =
    fraction_quotient_projection (fraction_pair_add hDomain p q).
Proof. apply:fraction_quotient_add_compatible;exact:fraction_quotient_repr. Qed.

(** Source for [fraction_quotient_opp_projection]: negation
    has the original fraction formula, supporting 3.4.7, p. 325. *)
Lemma fraction_quotient_opp_projection (p:P):
  fraction_quotient_opp (fraction_quotient_projection p) =
    fraction_quotient_projection (fraction_pair_opp p).
Proof. apply:fraction_quotient_opp_compatible;exact:fraction_quotient_repr. Qed.

(** Source for [fraction_quotient_multiply_projection]: multiplication
    has the original fraction formula, supporting 3.4.7, p. 325. *)
Lemma fraction_quotient_multiply_projection (p q:P):
  fraction_quotient_multiply (fraction_quotient_projection p) (fraction_quotient_projection q) =
    fraction_quotient_projection (fraction_pair_multiply hDomain p q).
Proof. apply:fraction_quotient_multiply_compatible;exact:fraction_quotient_repr. Qed.
End Quotient.
