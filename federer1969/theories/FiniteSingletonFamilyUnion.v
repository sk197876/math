(** Federer (1969), 3.2.41, printed p. 277: the base
    of finite-family induction reduces the union of a singleton
    index family to its actual member. *)
From mathcomp Require Import all_boot all_order classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_singleton_index_family_union]: supporting
    base case of the finite disjoint-family proof in Federer
    3.2.41, p. 277. An actual index retains the nonempty-family
    requirement, while the size bound forces all indices equal. *)
Lemma finite_singleton_index_family_union (I:finType) (X:Type)
    (G:I->set X) (i0:I):
  (#|I|<=1)%N ->(\bigcup_i G i)=G i0.
Proof.
move=> hCard.
have hAll (i:I): i = i0.
  have hPred:=(elimT (@card_le1P I predT) hCard) i0 (erefl true).
  apply/eqP; have h:=hPred i; by rewrite inE in h.
apply/seteqP; split.
- move=> x [i _ hi]; by rewrite (hAll i) in hi.
- move=> x hi; by exists i0.
Qed.
