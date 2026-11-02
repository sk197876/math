(** Federer (1969), 2.2.1, p. 59: complement closure makes countable-union
    and nonempty countable-intersection closure equivalent, provided the
    empty set is present. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
From Federer Require Import BorelFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_family_of_union]: Federer 2.2.1,
    p. 59, redundancy assertion: the empty set, relative complement
    and countable unions imply the printed intersection condition.
    The nonempty intersection lies in X because any one member does. *)
Lemma borel_family_of_union (I : choiceType) (X : set I) (F : set (set I)) :
  F set0 -> (forall A, F A -> A `<=` X) ->
  (forall A, F A -> F (X `\` A)) ->
  (forall G : set (set I), G `<=` F -> countable G -> F (\bigcup_(A in G) A)) ->
  is_borel_family X F.
Proof.
move=> h0 hw hc hu; constructor=> //.
move=> G hG hGc [A0 hA0].
pose H := (fun A => X `\` A) @` G.
have hHF : H `<=` F by move=> B [A hA <-]; exact: hc (hG A hA).
have hHc : countable H := sub_countable (card_image_le _ G) hGc.
have he : (\bigcap_(A in G) A) = X `\` (\bigcup_(B in H) B).
  apply/seteqP; split.
  - move=> x hx; split; first exact: hw A0 (hG A0 hA0) x (hx A0 hA0).
    by move=> [B [A hA <-] [_ hn]]; exact: hn (hx A hA).
  - move=> x [hx hn] A hA; apply: contrapT=> hnA; apply: hn.
    exists (X `\` A); first by exists A.
    by split.
rewrite he; exact: hc (hu H hHF hHc).
Qed.

(** Source for [borel_family_of_intersection]: Federer 2.2.1,
    p. 59, converse redundancy assertion: relative complement
    and nonempty countable intersections imply nonempty countable
    unions; the empty union uses the separately required empty member. *)
Lemma borel_family_of_intersection (I : choiceType) (X : set I) (F : set (set I)) :
  F set0 -> (forall A, F A -> A `<=` X) ->
  (forall A, F A -> F (X `\` A)) ->
  (forall G : set (set I), G `<=` F -> countable G ->
    (exists A, G A) -> F (\bigcap_(A in G) A)) -> is_borel_family X F.
Proof.
move=> h0 hw hc hi; refine (@borel_family_of_union I X F h0 hw hc _).
move=> G hG hGc; case: (pselect (exists A, G A))=> [[A0 hA0]|hn].
- pose H := (fun A => X `\` A) @` G.
  have hHF : H `<=` F by move=> B [A hA <-]; exact: hc (hG A hA).
  have hHc : countable H := sub_countable (card_image_le _ G) hGc.
  have hHn : exists B, H B by exists (X `\` A0); exists A0.
  have he : (\bigcup_(A in G) A) = X `\` (\bigcap_(B in H) B).
    apply/seteqP; split.
    + move=> x [A hA hx]; split; first exact: hw A (hG A hA) x hx.
      move=> h; have hb : H (X `\` A) by exists A.
      exact: (h _ hb).2 hx.
    + move=> x [hx hnI]; apply: contrapT=> hnU; apply: hnI.
      move=> B [A hA <-]; split=> //; move=> hA'; apply: hnU; by exists A.
  rewrite he; exact: hc (hi H hHF hHc hHn).
- have he : G = set0.
    apply/seteqP; split=> [A hA|A []]; exfalso; apply: hn; by exists A.
  by rewrite he bigcup_set0.
Qed.
