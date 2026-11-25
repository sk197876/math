(** General set theory supporting the univalent sequence of
    selected centers in Federer (1969), 3.1.20, p. 232. Empty
    slots handle finite or empty selections without repetition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_countable_partial_enumeration]: the injective
    sequence of the selected set S in Federer 3.1.20, p. 232.
    Some s denotes an active center; None is an inactive slot. *)
Record is_countable_partial_enumeration (J:choiceType) (S:set J) (eta:nat->option J) : Prop := {
  (** Source for [partial_enumeration_members]: every active
      sequence value belongs to S, 3.1.20, p. 232. *)
  partial_enumeration_members : forall i s,eta i = Some s -> S s;
  (** Source for [partial_enumeration_cover]: every selected
      center appears, 3.1.20, p. 232. *)
  partial_enumeration_cover : forall s,S s -> exists i,eta i = Some s;
  (** Source for [partial_enumeration_unique]: active centers
      are not repeated, the univalent sequence in 3.1.20, p. 232. *)
  partial_enumeration_unique : forall i j s,eta i = Some s -> eta j = Some s -> i = j
}.

(** Source for [countable_partial_enumeration_exists]: supporting
    the univalent indexing in Federer 3.1.20, p. 232. An
    injection into the natural numbers gives a partial enumeration,
    including finite and empty selected sets. *)
Lemma countable_partial_enumeration_exists (J:choiceType) (S:set J) : countable S ->
  exists eta,is_countable_partial_enumeration S eta.
Proof.
move=>/countable_injP [g hg].
pose E:=fun i s=>S s /\ g s = i.
pose eta:=fun i=>if pselect (exists s,E i s) is left h
  then Some (projT1 (cid h)) else None.
have he i s:eta i = Some s -> S s /\ g s = i.
  rewrite /eta; case:pselect=>[h|hn]; last by [].
  move=>hs.
  have hsame:projT1 (cid h) = s by case:hs.
  rewrite -hsame; exact: projT2 (cid h).
exists eta; constructor.
- move=>i s hs; exact (he i s hs).1.
- move=>s hs; exists (g s); rewrite /eta; case:pselect=>[h|hn].
  + have hp:=projT2 (cid h).
    have hsame:projT1 (cid h) = s:=@hg (projT1 (cid h)) s (mem_set hp.1) (mem_set hs) hp.2.
    by rewrite hsame.
  + exfalso; apply: hn; exists s; by split.
- move=>i j s hi hj; exact (eq_trans (esym (he i s hi).2) (he j s hj).2).
Qed.

(** Source for [partial_enumeration_finite_inverse]: a finite
    set of selected centers occupies finitely many active slots,
    supporting the finite-influence argument of Federer 3.1.20,
    p. 233. Univalence is essential here. *)
Lemma partial_enumeration_finite_inverse (J:choiceType) (S M:set J) eta :
  is_countable_partial_enumeration S eta -> M `<=` S -> finite_set M ->
  finite_set [set i|exists s,eta i = Some s /\ M s].
Proof.
move=>he hMS hM.
have hex s:exists i,S s -> eta i = Some s.
  case:(pselect (S s))=>[hs|hs].
  - have [i hi]:=@partial_enumeration_cover J S eta he s hs; by exists i.
  - exists 0%N=>ha; by exfalso; exact: hs ha.
have [idx hidx]:=choice hex.
have hEq:[set i|exists s,eta i = Some s /\ M s] = idx @` M.
  apply/seteqP; split=>i.
  - move=>[s [hi hs]]; exists s=>//.
    exact: esym (@partial_enumeration_unique J S eta he i (idx s) s hi (hidx s (hMS s hs))).
  - move=>[s hs <-]; exists s; split=>//; exact: hidx (hMS s hs).
rewrite hEq; exact: finite_image idx hM.
Qed.
