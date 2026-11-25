(** Federer (1969), 2.5.10, p. 101: adjoining a nonempty eligible compact
    set disjoint from the maximal family yields the contradiction. This
    supporting set lemma uses only the abstract maximality laws; the
    eligibility predicate is arbitrary. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import CountablyClosedFamilyUP MaximalDisjointFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [maximal_disjoint_family_no_new_piece]: the maximality
    contradiction in Federer 2.5.10, p. 101 An eligible set disjoint from
    every existing member must be empty. *)
Lemma maximal_disjoint_family_no_new_piece (X : choiceType) (P G : set (set X)) (Z : set X) :
  is_maximal_disjoint_family P G -> P Z ->
  (forall K, G K -> K `&` Z=set0) -> Z=set0.
Proof.
move=> hG hZ hd; pose F := G `|` [set Z].
have hFP : F `<=` P.
  move=> K [hk|he]; first exact: (@maximal_disjoint_family_members X P G hG K hk).
  by move: he=> /= ->.
have hFd : set_family_disjoint F.
  move=> K L [hk|hk] [hl|hl] hne.
  - exact: (@maximal_disjoint_family_disjoint X P G hG K L hk hl hne).
  - move: hl=> /= ->; exact: hd.
  - move: hk=> /= ->; rewrite setIC; exact: hd.
  - exfalso; apply: hne; exact: eq_trans hk (esym hl).
have hGF : G `<=` F by move=> K hk; left.
have hFG := (@maximal_disjoint_family_maximal X P G hG F hFP hFd hGF).
have hZG : G Z by apply: hFG; right.
by have := hd Z hZG; rewrite setIid.
Qed.
