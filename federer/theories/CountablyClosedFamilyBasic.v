(** Federer (1969), 2.2.1, p. 60: supporting indexed closure laws for the
    families used in the two generation criteria. Source context and boolean
    convention: CountablyClosedFamilyUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
From Federer Require Import BorelFamilyUP CountablyClosedFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_family_countably_closed]: Federer
    2.2.1, p. 60: every Borel family belongs to both weaker
    classes, with or without disjointness required for unions. *)
Lemma borel_family_countably_closed (d : bool) (I : choiceType)
    (X : set I) (F : set (set I)) :
  is_borel_family X F -> is_countably_closed_family d X F.
Proof.
move=> hF; constructor.
- exact: borel_family_empty hF.
- exact: borel_family_within hF.
- move=> G hG hc _; exact: (@borel_family_countable_union I X F hF G hG hc).
- exact: borel_family_countable_intersection hF.
Qed.

(** Source for [countably_closed_indexed_intersection]: Federer
    2.2.1(3), pp. 59-60, supporting indexed version for the
    two weaker classes. The index set is countable and nonempty. *)
Lemma countably_closed_indexed_intersection (d : bool) (I J : choiceType)
    (X : set I) (F : set (set I)) (hF : is_countably_closed_family d X F)
    (D : set J) (G : J -> set I) : countable D -> (exists j, D j) ->
  (forall j, D j -> F (G j)) -> F (\bigcap_(j in D) G j).
Proof.
move=> hD [j0 hj0] hG.
have he : (\bigcap_(j in D) G j) = \bigcap_(A in G @` D) A.
  apply/seteqP; split.
  - by move=> x hx A [j hj <-]; exact: hx j hj.
  - move=> x hx j hj; apply: hx; by exists j.
rewrite he; apply: (countably_closed_family_intersection hF).
- by move=> A [j hj <-]; exact: hG.
- exact: sub_countable (card_image_le G D) hD.
- exists (G j0); by exists j0.
Qed.

(** Source for [countably_closed_disjoint_indexed_union]: Federer
    2.2.1(2)', p. 60, supporting indexed disjoint-union closure,
    also available when the stronger union clause is selected. *)
Lemma countably_closed_disjoint_indexed_union (d : bool) (I J : choiceType)
    (X : set I) (F : set (set I)) (hF : is_countably_closed_family d X F)
    (D : set J) (G : J -> set I) : countable D ->
  (forall j, D j -> F (G j)) ->
  (forall j k, D j -> D k -> j <> k -> G j `&` G k = set0) ->
  F (\bigcup_(j in D) G j).
Proof.
move=> hD hG hd.
have he : (\bigcup_(j in D) G j) = \bigcup_(A in G @` D) A.
  apply/seteqP; split.
  - move=> x [j hj hx]; exists (G j)=> //; by exists j.
  - by move=> x [A [j hj <-] hx]; exists j.
rewrite he; apply: (countably_closed_family_union hF).
- by move=> A [j hj <-]; exact: hG.
- exact: sub_countable (card_image_le G D) hD.
- move=> _ A B [j hj <-] [k hk <-] hn; apply: hd=> //.
  by move=> hejk; apply: hn; rewrite hejk.
Qed.

(** Source for [countably_closed_binary_intersection]: Federer
    2.2.1(3), p. 59, two-set instance supporting the disjoint
    refinement on p. 60. It applies in either weaker class. *)
Lemma countably_closed_binary_intersection (d : bool) (I : choiceType)
    (X : set I) (F : set (set I)) (hF : is_countably_closed_family d X F)
    (A B : set I) : F A -> F B -> F (A `&` B).
Proof.
move=> hA hB.
have he : A `&` B = \bigcap_(b in @setT bool) (if b then A else B).
  apply/seteqP; split.
  - by move=> x [ha hb] [] _.
  - move=> x hx; split; [exact: hx true Logic.I|exact: hx false Logic.I].
rewrite he; apply: (countably_closed_indexed_intersection hF).
- exact: finite_set_countable (@finite_finset _ (@setT bool)).
- by exists true.
- by move=> [] _.
Qed.

(** Source for [countably_closed_indexed_union]: Federer
    2.2.1(2), pp. 59-60, arbitrary countable indexed unions
    in the stronger closure class. No disjointness is assumed. *)
Lemma countably_closed_indexed_union (I J : choiceType)
    (X : set I) (F : set (set I)) (hF : is_countably_closed_family false X F)
    (D : set J) (G : J -> set I) : countable D ->
  (forall j, D j -> F (G j)) -> F (\bigcup_(j in D) G j).
Proof.
move=> hD hG.
have he : (\bigcup_(j in D) G j) = \bigcup_(A in G @` D) A.
  apply/seteqP; split.
  - move=> x [j hj hx]; exists (G j)=> //; by exists j.
  - by move=> x [A [j hj <-] hx]; exists j.
rewrite he; apply: (countably_closed_family_union hF).
- by move=> A [j hj <-]; exact: hG.
- exact: sub_countable (card_image_le G D) hD.
- by [].
Qed.
