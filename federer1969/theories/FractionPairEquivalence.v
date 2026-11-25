(** Federer (1969), 3.4.7, p. 325: supporting
    field-of-fractions construction for the Gauss argument.
    Only the background set quotient will be imported;
    the fraction equivalence is proved from the domain law. *)
From mathcomp Require Import all_boot all_order ssralg boolp ring.
From Federer Require Import CommutativeDomainUP CommutativeDomainCancellation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Fractions.
Variable A:comNzRingType.
Hypothesis hDomain:is_commutative_integral_domain A.

(** Source for [nonzero_denominator_pair]: numerator and
    nonzero denominator for a private existence witness,
    supporting the Gauss lemma in 3.4.7, p. 325. *)
Definition nonzero_denominator_pair:= {p:A*A |p.2!=0}.

(** Source for [fraction_pair_relation]: cross multiplication
    defines the fraction equivalence, supporting 3.4.7, p. 325. *)
Definition fraction_pair_relation (p q:nonzero_denominator_pair):bool:=
  (val p).1*(val q).2==(val q).1*(val p).2.

(** Source for [fraction_pair_relation_refl]: reflexivity of
    fraction equivalence, supporting 3.4.7, p. 325. *)
Lemma fraction_pair_relation_refl:reflexive fraction_pair_relation.
Proof. move=>p;exact:eqxx. Qed.

(** Source for [fraction_pair_relation_sym]: symmetry of
    fraction equivalence, supporting 3.4.7, p. 325. *)
Lemma fraction_pair_relation_sym:symmetric fraction_pair_relation.
Proof. move=>p q;exact:eq_sym. Qed.

(** Source for [fraction_pair_relation_trans]: transitivity of
    fraction equivalence, supporting 3.4.7, p. 325.
    The middle denominator is cancelled by the domain law. *)
Lemma fraction_pair_relation_trans:transitive fraction_pair_relation.
Proof.
move=>q p r /eqP hPQ /eqP hQR;apply/eqP.
have hDen:(val q).2<>0 by apply/eqP;exact:valP q.
apply:(@commutative_domain_cancel_left A hDomain (val q).2 _ _ hDen).
transitivity (((val p).1*(val q).2)*(val r).2);first ring.
rewrite hPQ.
transitivity (((val q).1*(val r).2)*(val p).2);first ring.
rewrite hQR;ring.
Qed.
End Fractions.
