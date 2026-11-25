(** Federer (1969), 2.2.1, pp. 59-60: elementary Borel family laws and
    indexed closure. Source context and union conventions: BorelFamilyUP.v.
    These supporting indexed forms allow repeated sets in a family without
    changing its union. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
From Federer Require Import BorelFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_family_whole]: Federer 2.2.1, p. 59, every Borel
    family contains X, as the relative complement of its empty member *)
Lemma borel_family_whole (I : choiceType) (X : set I) (F : set (set I)) :
  is_borel_family X F -> F X.
Proof.
move=> hF; have h := borel_family_complement hF (borel_family_empty hF).
by rewrite setD0 in h.
Qed.

(** Source for [borel_family_indexed_union]: Federer 2.2.1(2),
    p. 59, supporting indexed form of countable-union closure.
    Countability of the index set implies countability of its image
    family; repetitions and the empty index set are allowed. *)
Lemma borel_family_indexed_union (I J : choiceType) (X : set I)
    (F : set (set I)) (hF : is_borel_family X F) (D : set J) (G : J -> set I) :
  countable D -> (forall j, D j -> F (G j)) -> F (\bigcup_(j in D) G j).
Proof.
move=> hD hG.
have he : (\bigcup_(j in D) G j) = \bigcup_(A in G @` D) A.
  apply/seteqP; split.
  - move=> x [j hj hx]; exists (G j)=> //; by exists j.
  - by move=> x [A [j hj <-] hx]; exists j.
rewrite he; apply: (borel_family_countable_union hF).
- by move=> A [j hj <-]; exact: hG.
- exact: sub_countable (card_image_le G D) hD.
Qed.

(** Source for [borel_family_indexed_intersection]: Federer
    2.2.1(3), p. 59, supporting indexed form of intersection
    closure. A member of the nonempty index set ensures the result
    is a subset of X even when X is a proper ambient subset. *)
Lemma borel_family_indexed_intersection (I J : choiceType) (X : set I)
    (F : set (set I)) (hF : is_borel_family X F) (D : set J) (G : J -> set I) :
  countable D -> (exists j, D j) ->
  (forall j, D j -> F (G j)) -> F (\bigcap_(j in D) G j).
Proof.
move=> hD [j0 hj0] hG.
have he : (\bigcap_(j in D) G j) = \bigcap_(A in G @` D) A.
  apply/seteqP; split.
  - by move=> x hx A [j hj <-]; exact: hx j hj.
  - move=> x hx j hj; apply: hx; by exists j.
rewrite he; apply: (borel_family_countable_intersection hF).
- by move=> A [j hj <-]; exact: hG.
- exact: sub_countable (card_image_le G D) hD.
- exists (G j0); by exists j0.
Qed.

(** Source for [borel_family_binary_union]: Federer 2.2.1(2),
    p. 59, supporting two-member special case of countable closure. *)
Lemma borel_family_binary_union (I : choiceType) (X : set I)
    (F : set (set I)) (hF : is_borel_family X F) (A B : set I) :
  F A -> F B -> F (A `|` B).
Proof.
move=> hA hB.
have he : A `|` B = \bigcup_(b in @setT bool) (if b then A else B).
  apply/seteqP; split.
  - move=> x [hx|hx]; [by exists true|by exists false].
  - by move=> x [[] _ hx]; [left|right].
rewrite he; apply: (borel_family_indexed_union hF).
- exact: finite_set_countable (@finite_finset _ (@setT bool)).
- by move=> [] _.
Qed.

(** Source for [borel_family_binary_intersection]: Federer
    2.2.1(3), p. 59, supporting two-member special case of
    nonempty countable-intersection closure. *)
Lemma borel_family_binary_intersection (I : choiceType) (X : set I)
    (F : set (set I)) (hF : is_borel_family X F) (A B : set I) :
  F A -> F B -> F (A `&` B).
Proof.
move=> hA hB.
have he : A `&` B = \bigcap_(b in @setT bool) (if b then A else B).
  apply/seteqP; split.
  - by move=> x [ha hb] [] _.
  - move=> x hx; split; [exact: hx true Logic.I|exact: hx false Logic.I].
rewrite he; apply: (borel_family_indexed_intersection hF).
- exact: finite_set_countable (@finite_finset _ (@setT bool)).
- by exists true.
- by move=> [] _.
Qed.

(** Source for [borel_family_difference]: Federer 2.2.1(1),(3),
    p. 59, supporting relative difference closure, used in the
    disjoint-increment argument on p. 60. *)
Lemma borel_family_difference (I : choiceType) (X : set I)
    (F : set (set I)) (hF : is_borel_family X F) (A B : set I) :
  F A -> F B -> F (A `\` B).
Proof.
move=> hA hB.
have he : A `\` B = A `&` (X `\` B).
  apply/seteqP; split=> [x [ha hb]|x [ha [_ hb]]]; last by split.
  split=> //; split=> //; exact: (@borel_family_within I X F hF A hA x ha).
rewrite he; exact: (@borel_family_binary_intersection I X F hF A (X `\` B) hA
  (@borel_family_complement I X F hF B hB)).
Qed.
