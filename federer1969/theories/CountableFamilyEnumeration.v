(** Set-theoretic infrastructure for Federer (1969), 2.2.2, p. 61: transfer
    sequence intersections to nonempty countable families. Unlike
    zero-filled enumeration for unions, a missing index repeats a fixed
    original member, so intersections are preserved. Source context:
    ClosedApproximationUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_nonempty_family_enumeration]: supporting
    set theory for Federer 2.2.2, p. 61. Every nonempty countable
    family has a sequence enumeration with exactly the same members,
    permitting repetition and covering finite families as well. *)
Lemma countable_nonempty_family_enumeration (I J : choiceType)
    (D : set J) (F : J -> set I) : countable D -> (exists j, D j) ->
  exists G : nat -> set I, G @` setT = F @` D.
Proof.
move=> /countable_injP[g hg] [j0 hj0].
have hc n : exists j, D j /\ forall k, D k -> g k = n -> j = k.
  case: (pselect (exists j, D j /\ g j = n))=> [[j [hj he]]|hn].
  - exists j; split=> // k hk hek; apply: hg.
    + exact: mem_set hj.
    + exact: mem_set hk.
    + by rewrite he hek.
  - exists j0; split=> // k hk hek; exfalso; apply: hn; exists k; by split.
pose j n := projT1 (cid (hc n)).
have hj n : D (j n) /\ forall k, D k -> g k = n -> j n = k.
  exact: projT2 (cid (hc n)).
exists (fun n => F (j n)); apply/seteqP; split.
- move=> A [n _ <-]; exists (j n)=> //; exact: (hj n).1.
- move=> A [k hk <-]; exists (g k); first exact Logic.I.
  by rewrite ((hj (g k)).2 k hk (erefl _)).
Qed.

(** Source for [countable_nonempty_intersection_sequence]: Federer
    2.2.2, p. 61, supporting equivalence of the nonempty countable
    family and sequence intersection formulations. Every sequence term
    is an original member and no empty padding is introduced. *)
Lemma countable_nonempty_intersection_sequence (I J : choiceType)
    (D : set J) (F : J -> set I) : countable D -> (exists j, D j) ->
  exists G : nat -> set I,
    (forall n, exists j, D j /\ G n = F j) /\
    (\bigcap_n G n) = \bigcap_(j in D) F j.
Proof.
move=> hc hn; have [G he] := countable_nonempty_family_enumeration F hc hn.
exists G; split.
- move=> n; have hg : (G @` setT) (G n) by exists n.
  rewrite he in hg; have [j hj heq] := hg; exists j; split=> //; exact: esym heq.
- apply/seteqP; split.
  + move=> x hx j hj; have hg : (F @` D) (F j) by exists j.
    rewrite -he in hg; have [n _ hen] := hg; rewrite -hen; exact: hx n Logic.I.
  + move=> x hx n _; have hg : (G @` setT) (G n) by exists n.
    rewrite he in hg; have [j hj hej] := hg; rewrite -hej; exact: hx j hj.
Qed.
