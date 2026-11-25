(** Private carrier construction supporting Federer (1969),
    3.4.8(5), p. 328, and the Rees ring in Bourbaki,
    Commutative Algebra (1972), Chapter III, section 3,
    no. 1, Lemma 1, p. 197. The hierarchy factories
    transfer the proved original operation laws to the
    member subtype; they supply no mathematical Noetherian theorem.
    Downstream mathematics uses the sealed realisation laws. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeSubringUP CommutativeSubringRealisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Carrier.
Variable A:comNzRingType.
Variable S:set A.
Hypothesis hS:is_commutative_subring S.

(** Source for [subring_member_predicate]: the original
    subring membership, supporting the cited Rees-ring Lemma 1. *)
Definition subring_member_predicate (x:A):bool:=asbool (S x).

(** Source for [subring_member_carrier]: a private member
    subtype used only to prove existence of the independent
    subring realisation, supporting the cited Lemma 1. *)
Record subring_member_carrier:=SubringMember {
  (** Source for [subring_member_value]: the original
      ambient value, supporting the cited Lemma 1. *)
  subring_member_value:A;
  (** Source for [subring_member_proof]: membership in
      the original subring, supporting the cited Lemma 1. *)
  subring_member_proof:subring_member_predicate subring_member_value
}.

(** Source for [subring_member_rect]: dependent elimination
    of the private subtype, supporting the cited Lemma 1. *)
Definition subring_member_rect (P:subring_member_carrier->Type)
    (h:forall x hx,P (@SubringMember x hx)) (z:subring_member_carrier):P z:=
  match z as z' return P z' with @SubringMember x hx=>h x hx end.
HB.instance Definition _ := [isSub for subring_member_value by subring_member_rect].
HB.instance Definition _ := [Choice of subring_member_carrier by <:].

(** Source for [subring_member_predicate_closed]: the
    original subring laws preserve one, differences and
    products, supporting the cited Rees-ring Lemma 1. *)
Lemma subring_member_predicate_closed:GRing.subring_closed subring_member_predicate.
Proof.
split.
- apply/asboolP;exact:commutative_subring_one hS.
- move=>x y /asboolP hx /asboolP hy;apply/asboolP.
  exact:(@commutative_subring_add A S hS x (-y) hx (@commutative_subring_opp A S hS y hy)).
- move=>x y /asboolP hx /asboolP hy;apply/asboolP.
  exact:(@commutative_subring_multiply A S hS x y hx hy).
Qed.
HB.instance Definition _ := GRing.SubChoice_isSubComNzRing.Build A
  subring_member_predicate subring_member_carrier subring_member_predicate_closed.

(** Source for [subring_member_ring]: the private packed
    ring supplied by the original subring laws,
    supporting the cited Rees-ring Lemma 1. *)
Definition subring_member_ring:comNzRingType:=[the comNzRingType of subring_member_carrier].

(** Source for [subring_member_value_additive]: the
    original inclusion preserves zero and addition,
    supporting the cited Rees-ring Lemma 1. *)
Lemma subring_member_value_additive:nmod_morphism subring_member_value.
Proof.
split.
- change ((val (0:subring_member_carrier):A)=0);exact:rmorph0.
- move=>x y;change ((val (x+y):A)=val x+val y);exact:rmorphD.
Qed.
HB.instance Definition _ := GRing.isNmodMorphism.Build subring_member_carrier A
  subring_member_value subring_member_value_additive.

(** Source for [subring_member_value_multiplicative]: the
    original inclusion preserves one and multiplication,
    supporting the cited Rees-ring Lemma 1. *)
Lemma subring_member_value_multiplicative:monoid_morphism subring_member_value.
Proof.
split.
- change ((val (1:subring_member_carrier):A) = 1);exact:rmorph1.
- move=>x y;change ((val (x*y):A)=val x*val y);exact:rmorphM.
Qed.
HB.instance Definition _ := GRing.isMonoidMorphism.Build subring_member_carrier A
  subring_member_value subring_member_value_multiplicative.

(** Source for [subring_member_inclusion]: the private
    original inclusion as a ring homomorphism, supporting
    the cited Rees-ring Lemma 1. *)
Definition subring_member_inclusion:
    {rmorphism [the comNzRingType of subring_member_carrier]->A}:=
  GRing.RMorphism.clone _ _ subring_member_value _.

(** Source for [subring_member_realisation]: the private
    carrier satisfies the independent exact image and
    injection laws, supporting the cited Rees-ring Lemma 1. *)
Lemma subring_member_realisation:is_commutative_subring_realisation S subring_member_inclusion.
Proof.
constructor;first exact:val_inj.
move=>a;split.
- move=>ha;exists (@SubringMember a (introT (asboolP _) ha));reflexivity.
- move=>[c <-];apply/asboolP;exact:subring_member_proof.
Qed.
End Carrier.
