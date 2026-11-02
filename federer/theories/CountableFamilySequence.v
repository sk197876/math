(** Set-theoretic infrastructure for Federer (1969), 2.2.1, p. 60: transfer
    the sequence disjointification argument to a general countable family.
    The same zero-filled enumeration is used in the locally proved 2.1.3
    closure argument. Source context: BorelFamilyUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_family_as_sequence]: supporting
    infrastructure for Federer 2.2.1, p. 60, disjointification.
    A countable indexed union is a sequence union; each sequence
    member is an original set or an empty gap. No inhabitant of
    the index set is required, so the empty-family case is retained. *)
Lemma countable_family_as_sequence (I J : choiceType) (D : set J) (F : J -> set I) :
  countable D -> exists G : nat -> set I,
    (forall n, G n = set0 \/ exists j, D j /\ G n = F j) /\
    (\bigcup_n G n) = \bigcup_(j in D) F j.
Proof.
move=> /countable_injP[g hg].
pose G n := \bigcup_(j in D `&` [set j | g j == n]) F j.
exists G; split.
- move=> n; case: (pselect (exists j, D j /\ g j == n))=> [[j [hj hjn]]|hn].
  + right; exists j; split=> //; apply/seteqP; split.
    * move=> x [k [hk hkn] hx].
      have hkj : k = j.
        apply: hg; [exact: mem_set hk|exact: mem_set hj|].
        by move/eqP: hkn=> ->; move/eqP: hjn=> ->.
      by rewrite -hkj.
    * move=> x hx; exists j=> //; by split.
  + left; apply/seteqP; split=> [x [j [hj hjn] _]|x []].
    exfalso; apply: hn; by exists j.
- apply/seteqP; split.
  + by move=> x [n _ [j [hj _] hx]]; exists j.
  + move=> x [j hj hx]; exists (g j); first exact Logic.I.
    exists j=> //; by split=> //; rewrite /= eqxx.
Qed.
