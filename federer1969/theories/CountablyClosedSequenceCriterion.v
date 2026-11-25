(** Set-theoretic background for Federer (1969), 2.2.10, p. 66: the sequence
    closure arguments imply the family hypotheses used in 2.2.1. A sparse
    enumeration preserves disjointness, including finite and empty families.
    Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
From Federer Require Import CountablyClosedFamilyUP CountableFamilyEnumeration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [disjoint_sequence_closure_family]: supporting
    transfer from sequences to countable families in Federer
    2.2.10, p. 66. Empty gaps ensure that distinct nonempty
    sequence terms represent distinct original members. Repeated
    enumeration would not suffice for the disjoint-union hypothesis. *)
Lemma disjoint_sequence_closure_family (T : choiceType) (F : set (set T)) :
  F set0 ->
  (forall S : nat -> set T, (forall i, F (S i)) ->
    (forall i j x, S i x -> S j x -> i = j) -> F (\bigcup_i S i)) ->
  (forall S : nat -> set T, (forall i, F (S i)) -> F (\bigcap_i S i)) ->
  is_countably_closed_family true setT F.
Proof.
move=> h0 hu hi; constructor.
- exact h0.
- move=> A _; exact: subsetT.
- move=> G hG /countable_injP[encode henc] hdis.
  pose S n := \bigcup_(A in G `&` [set A | encode A == n]) A.
  have hs n : F (S n).
    case: (pselect (exists A, G A /\ encode A == n))=> [[A [hA hen]]|hn].
    + have he : S n = A.
        apply/seteqP; split.
        * move=> x [B [hB heb] hx].
          have hBA : B = A.
            apply: henc; [exact: mem_set hB|exact: mem_set hA|].
            by move/eqP: heb=> ->; move/eqP: hen=> ->.
          by rewrite -hBA.
        * move=> x hx; exists A=> //; by split.
      rewrite he; exact: hG A hA.
    + have he : S n = set0.
        apply/seteqP; split=> [x [A [hA hen] hx]|x []].
        exfalso; apply: hn; by exists A.
      by rewrite he.
  have hd : forall i j x, S i x -> S j x -> i = j.
    move=> i j x [A [hA /eqP heA] hx] [B [hB /eqP heB] hy].
    have hAB : A = B.
      apply: contrapT=> hne.
      have he := hdis erefl A B hA hB hne.
      have hh : (A `&` B) x by split.
      by rewrite he in hh.
    by rewrite -heA -heB hAB.
  have he : (\bigcup_i S i) = \bigcup_(A in G) A.
    apply/seteqP; split.
    + by move=> x [i _ [A [hA _] hx]]; exists A.
    + move=> x [A hA hx]; exists (encode A)=> //; exists A=> //; by split=> //; rewrite /= eqxx.
  rewrite -he; exact: hu hs hd.
- move=> G hG hc hn.
  have [S [hs he]] := @countable_nonempty_intersection_sequence T
    [the choiceType of set T] G id hc hn.
  rewrite -he; apply: hi=> i; have [A [hA ->]] := hs i; exact: hG A hA.
Qed.
