(** Federer (1969), 3.4.7, p. 325: private fraction
    arithmetic for the coefficient field in the Gauss argument.
    Operations and their compatibility are proved directly. *)
From mathcomp Require Import all_boot all_order ssralg boolp ring.
From Federer Require Import CommutativeDomainUP CommutativeDomainCancellation FractionPairEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Arithmetic.
Variable A:comNzRingType.
Hypothesis hDomain:is_commutative_integral_domain A.
Local Notation P:=(@nonzero_denominator_pair A).

(** Source for [fraction_pair_denominator_product]: product
    denominators remain nonzero in a domain, supporting
    the fraction construction for 3.4.7, p. 325. *)
Lemma fraction_pair_denominator_product (p q:P):(val p).2*(val q).2!=0.
Proof.
have hp:(val p).2<>0 by apply/eqP;exact:valP p.
have hq:(val q).2<>0 by apply/eqP;exact:valP q.
apply/eqP;exact:(commutative_domain_product_nonzero hDomain hp hq).
Qed.

(** Source for [fraction_pair_constant]: original scalars
    have denominator one, supporting 3.4.7, p. 325. *)
Definition fraction_pair_constant (a:A):P:=Sub (a,1) (oner_neq0 A).

(** Source for [fraction_pair_add]: actual fraction addition,
    supporting the existence proof in 3.4.7, p. 325. *)
Definition fraction_pair_add (p q:P):P:=
  Sub ((val p).1*(val q).2+(val q).1*(val p).2,(val p).2*(val q).2)
    (fraction_pair_denominator_product p q).

(** Source for [fraction_pair_opp]: actual fraction negation,
    supporting the existence proof in 3.4.7, p. 325. *)
Definition fraction_pair_opp (p:P):P:=Sub (- (val p).1,(val p).2) (valP p).

(** Source for [fraction_pair_multiply]: actual fraction
    multiplication, supporting 3.4.7, p. 325. *)
Definition fraction_pair_multiply (p q:P):P:=
  Sub ((val p).1*(val q).1,(val p).2*(val q).2)
    (fraction_pair_denominator_product p q).

(** Source for [fraction_pair_add_compatible]: equivalent
    fractions have equivalent sums, supporting the quotient
    construction for 3.4.7, p. 325. *)
Lemma fraction_pair_add_compatible (p q r s:P):
  fraction_pair_relation p r ->fraction_pair_relation q s ->
  fraction_pair_relation (fraction_pair_add p q) (fraction_pair_add r s).
Proof.
move=>/eqP hPR /eqP hQS;apply/eqP.
change (((val p).1*(val q).2+(val q).1*(val p).2)*((val r).2*(val s).2) =
  ((val r).1*(val s).2+(val s).1*(val r).2)*((val p).2*(val q).2)).
transitivity (((val p).1*(val r).2)*((val q).2*(val s).2)+
  ((val q).1*(val s).2)*((val p).2*(val r).2));first ring.
rewrite hPR hQS;ring.
Qed.

(** Source for [fraction_pair_opp_compatible]: equivalent
    fractions have equivalent negatives, supporting 3.4.7, p. 325. *)
Lemma fraction_pair_opp_compatible (p q:P):
  fraction_pair_relation p q ->
  fraction_pair_relation (fraction_pair_opp p) (fraction_pair_opp q).
Proof. move=>/eqP h;apply/eqP;change (- (val p).1*(val q).2 = - (val q).1*(val p).2);by rewrite !mulNr h. Qed.

(** Source for [fraction_pair_multiply_compatible]: equivalent
    fractions have equivalent products, supporting 3.4.7, p. 325. *)
Lemma fraction_pair_multiply_compatible (p q r s:P):
  fraction_pair_relation p r ->fraction_pair_relation q s ->
  fraction_pair_relation (fraction_pair_multiply p q) (fraction_pair_multiply r s).
Proof.
move=>/eqP hPR /eqP hQS;apply/eqP.
change (((val p).1*(val q).1)*((val r).2*(val s).2) =
  ((val r).1*(val s).1)*((val p).2*(val q).2)).
transitivity (((val p).1*(val r).2)*((val q).1*(val s).2));first ring.
rewrite hPR hQS;ring.
Qed.
End Arithmetic.
