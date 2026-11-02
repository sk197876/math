(** Federer (1969), 2.2.1, p. 60: the family H of sets whose complements
    also lie in F. The sequence of disjoint increments gives union closure
    even under the weaker clause (2)'. The required whole-set membership
    comes from the corrected empty-generator hypothesis; see erratum p. 1,
    book p. 60 line 4. Source context: BorelFamilyUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
From Federer Require Import BorelFamilyUP BorelFamilyRedundancy
  CountablyClosedFamilyUP CountablyClosedFamilyBasic CountableFamilySequence
  SetSequenceDisjointification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countably_closed_complement_core_sequence_union]:
    Federer 2.2.1, p. 60, displayed disjointification: the union
    of A_n equals the union of A_n intersected with all earlier
    complements. These increments lie in F and are disjoint;
    the complement of the union is the intersection of complements. *)
Lemma countably_closed_complement_core_sequence_union (d : bool)
    (I : choiceType) (X : set I) (F : set (set I))
    (hF : is_countably_closed_family d X F) (A : nat -> set I) :
  F X -> (forall n, F (A n) /\ F (X `\` A n)) ->
  F (\bigcup_n A n) /\ F (X `\` \bigcup_n A n).
Proof.
move=> hX hA.
have hp n : F (X `\` set_sequence_prefix A n).
  elim: n=> [|n IH]; first by rewrite set_sequence_prefix_zero setD0.
  rewrite set_sequence_prefix_succ.
  have he : X `\` (set_sequence_prefix A n `|` A n) =
      (X `\` set_sequence_prefix A n) `&` (X `\` A n).
    apply/seteqP; split.
    - move=> x [hx hn]; split; split=> //; move=> h; apply: hn; [by left|by right].
    - move=> x [[hx hp0] [_ ha]]; split=> //; by move=> [h|h]; [exact: hp0 h|exact: ha h].
  rewrite he; exact: (@countably_closed_binary_intersection d I X F hF _ _ IH (hA n).2).
have hD n : F (set_sequence_disjointify A n).
  have he : set_sequence_disjointify A n = A n `&` (X `\` set_sequence_prefix A n).
    apply/seteqP; split=> [x [hx hn]|x [hx [_ hn]]]; last by split.
    split=> //; split=> //; exact: (@countably_closed_family_within d I X F hF _ (hA n).1 x hx).
  rewrite he; exact: (@countably_closed_binary_intersection d I X F hF _ _ (hA n).1 (hp n)).
split.
- rewrite -set_sequence_disjointify_union.
  apply: (countably_closed_disjoint_indexed_union hF); first exact: countableP.
  + by move=> n _; exact: hD.
  + move=> n m _ _ hn; apply/seteqP; split=> [x [hxn hxm]|x []].
    apply: (@set_sequence_disjointify_disjoint I A n m _ x hxn hxm).
    exact/eqP.
- have he : X `\` (\bigcup_n A n) = \bigcap_n (X `\` A n).
    apply/seteqP; split.
    + move=> x [hx hn] n _; split=> //; move=> ha; apply: hn; by exists n.
    + move=> x hx; split; first exact: (hx 0%N Logic.I).1.
      move=> [n _ hn]; exact: (hx n Logic.I).2 hn.
  rewrite he; apply: (countably_closed_indexed_intersection hF); first exact: countableP.
  + by exists 0%N.
  + by move=> n _; exact: (hA n).2.
Qed.

(** Source for [countably_closed_complement_core_borel]: Federer
    2.2.1, p. 60: H is closed under complement and countable
    unionisation and intersection, hence is a Borel family. This
    supporting statement assumes X belongs to F explicitly; the
    corrected generation criterion below derives that fact from
    the empty generator. *)
Theorem countably_closed_complement_core_borel (d : bool) (I : choiceType)
    (X : set I) (F : set (set I)) (hF : is_countably_closed_family d X F) :
  F X -> is_borel_family X [set A | F A /\ F (X `\` A)].
Proof.
move=> hX; apply: borel_family_of_union.
- split; first exact: countably_closed_family_empty hF.
  by rewrite setD0.
- move=> A [hA _]; exact: (@countably_closed_family_within d I X F hF A hA).
- move=> A [hA hc]; split=> //.
  have he : X `\` (X `\` A) = A.
    apply/seteqP; split.
    + move=> x [hx hn]; apply: contrapT=> hnA; apply: hn; by split.
    + move=> x hx; split; first exact: (@countably_closed_family_within d I X F hF A hA x hx).
      by move=> [_ hn]; exact: hn hx.
  by rewrite he.
- move=> G hG hGc.
  have [A [hA he]] := @countable_family_as_sequence I _ G (fun A => A) hGc.
  rewrite -he; apply: (@countably_closed_complement_core_sequence_union d I X F hF A hX).
  move=> n; have [hz|[B [hB hb]]] := hA n.
  + rewrite hz; split; first exact: countably_closed_family_empty hF.
    by rewrite setD0.
  + rewrite hb; exact: hG B hB.
Qed.
