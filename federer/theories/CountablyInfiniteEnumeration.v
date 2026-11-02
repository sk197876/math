(** General set theory supporting Federer (1969), 2.2.9, p. 65: infinitely
    many disjoint interval children must be enumerated without repetition.
    This background lemma supplies a bijective enumeration from countability
    and an explicit injection of the natural numbers; it does not assume the
    desired family is infinite without proof. Source context:
    NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot boolp classical_sets functions cardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countably_infinite_enumeration]: supporting
    set-theoretic enumeration for Federer 2.2.9, p. 65.
    Unlike the cover enumeration in 2.2.8, this enumeration is
    injective as well as surjective, preserving sibling disjointness. *)
Lemma countably_infinite_enumeration (J : Type) (f : nat -> J) :
  countable (@setT J) -> injective f -> exists (encode : J -> nat)
    (decode : nat -> J), cancel encode decode /\ cancel decode encode.
Proof.
move=> hc hf.
have hi : infinite_set (@setT J).
  move=> hj; apply: infinite_nat.
  have hp : finite_set (f @^-1` (@setT J)).
    apply: finite_preimage _ hj; move=> i j _ _; exact: hf.
  by rewrite preimage_setT in hp.
have [e [_ he hs]] := elimT card_set_bijP (eq_card_nat hc hi).
have hex n : exists j, e j = n.
  have [j _ hj] := hs n Logic.I; by exists j.
pose d n := projT1 (cid (hex n)).
have hd n : e (d n) = n by exact: projT2 (cid (hex n)).
exists e, d; split=> // j; apply: he; try by rewrite inE.
exact: hd.
Qed.
