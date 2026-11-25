(** Private existence witness supporting Federer (1969),
    3.4.8(5), p. 328: a homomorphism whose values lie
    in a specified subring lifts to its ring carrier.
    Source: the original coefficient map into the Rees
    ring in Bourbaki, Commutative Algebra (1972),
    Chapter III, section 3, no. 1, Lemma 1, p. 197.
    Downstream proofs use the public existence theorem. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeSubringRealisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Lift.
Variables A B C:comNzRingType.
Variable S:set B.
Variable inclusion:{rmorphism C->B}.
Hypothesis hC:is_commutative_subring_realisation S inclusion.
Variable phi:{rmorphism A->B}.
Hypothesis hImage:forall a:A,S (phi a).

(** Source for [subring_lift_member_exists]: every original
    coefficient image has a member of the specified
    carrier above it, supporting the cited Lemma 1. *)
Local Lemma subring_lift_member_exists a:exists c:C,inclusion c=phi a.
Proof. exact:(@commutative_subring_inclusion_image B S C inclusion hC (phi a)).1 (hImage a). Qed.

(** Source for [subring_lift_function]: a private member
    choice used only to prove lift existence in the
    cited Rees-ring Lemma 1. *)
Definition subring_lift_function a:C:=projT1 (cid (subring_lift_member_exists a)).

(** Source for [subring_lift_function_equation]: the private
    member maps to the original coefficient value,
    supporting the cited Lemma 1. *)
Lemma subring_lift_function_equation a:inclusion (subring_lift_function a)=phi a.
Proof. exact:(projT2 (cid (subring_lift_member_exists a))). Qed.

(** Source for [subring_lift_function_additive]: injectivity
    of inclusion proves the additive lift laws,
    supporting the cited Lemma 1. *)
Lemma subring_lift_function_additive:nmod_morphism subring_lift_function.
Proof.
split.
- apply:(@commutative_subring_inclusion_injective B S C inclusion hC).
  by rewrite subring_lift_function_equation !rmorph0.
- move=>a b;apply:(@commutative_subring_inclusion_injective B S C inclusion hC).
  by rewrite rmorphD !subring_lift_function_equation rmorphD.
Qed.
HB.instance Definition _ := GRing.isNmodMorphism.Build A C
  subring_lift_function subring_lift_function_additive.

(** Source for [subring_lift_function_multiplicative]:
    injectivity of inclusion proves the unit and product
    lift laws, supporting the cited Lemma 1. *)
Lemma subring_lift_function_multiplicative:monoid_morphism subring_lift_function.
Proof.
split.
- apply:(@commutative_subring_inclusion_injective B S C inclusion hC).
  by rewrite subring_lift_function_equation !rmorph1.
- move=>a b;apply:(@commutative_subring_inclusion_injective B S C inclusion hC).
  by rewrite rmorphM !subring_lift_function_equation rmorphM.
Qed.
HB.instance Definition _ := GRing.isMonoidMorphism.Build A C
  subring_lift_function subring_lift_function_multiplicative.

(** Source for [subring_lift_ring_map]: the private
    lift has the original ring homomorphism laws,
    supporting the cited Lemma 1. *)
Definition subring_lift_ring_map:{rmorphism A->C}:=
  GRing.RMorphism.clone A C subring_lift_function _.
End Lift.
