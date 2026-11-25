(** Federer (1969), 2.6.2, p. 116: subtracting a measurable rectangle from a
    rectangle gives two disjoint measurable rectangles. Iterate this split
    over a finite disjoint family. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureFiniteClosure DisjointRectangleCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [rectangle_finite_disjoint_union]: the base family consisting
    of one member of P0 in the proof of Federer 2.6.2, p. 116 Empty
    rectangles are allowed. *)
Lemma rectangle_finite_disjoint_union (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (A : set X) (B : set Y) :
  measure_measurable alpha A -> measure_measurable beta B ->
  finite_disjoint_rectangle_union alpha beta (A `*` B).
Proof.
move=> hA hB; exists [set (A,B)]; split; first exact: finite_set1.
constructor.
- by move=> p ->; split.
- by move=> p q -> -> hn; exfalso; apply: hn.
- apply/seteqP; split=> [z hz|z [p -> hz]] //; by exists (A,B).
Qed.

(** Source for [finite_rectangle_union_difference]: the finite
    disjoint-union stability under subtraction of a rectangle used in
    Federer 2.6.2, p. 116 Each original rectangle is split into its
    first-factor difference and remaining second-factor difference. *)
Lemma finite_rectangle_union_difference (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (S : set (X * Y)) (C : set X) (D : set Y) :
  finite_disjoint_rectangle_union alpha beta S ->
  measure_measurable alpha C -> measure_measurable beta D ->
  finite_disjoint_rectangle_union alpha beta (S `\` (C `*` D)).
Proof.
move=> [G [hfin hg]] hC hD.
pose L (p : set X * set Y) := (p.1 `\` C, p.2).
pose T (p : set X * set Y) := (p.1 `&` C, p.2 `\` D).
pose H := (L @` G) `|` (T @` G).
have hl p z : ((L p).1 `*` (L p).2) z -> (p.1 `*` p.2) z.
  by move=> [[hx _] hy]; split.
have ht p z : ((T p).1 `*` (T p).2) z -> (p.1 `*` p.2) z.
  by move=> [[hx _] [hy _]]; split.
have heq p q z : G p -> G q -> (p.1 `*` p.2) z -> (q.1 `*` q.2) z -> p = q.
  move=> hp hq hzp hzq; apply: contrapT=> hn.
  exact: (@disjoint_rectangle_pieces R X Y alpha beta G S hg p q hp hq hn z hzp hzq).
exists H; split.
- rewrite /H finite_setU; split; exact: finite_image hfin.
- constructor.
  + move=> p [[q hq <-]|[q hq <-]]; have [hq1 hq2] := disjoint_rectangle_factors hg hq.
    * split=> //; exact (@measure_measurable_difference R X alpha ha q.1 C hq1 hC).
    * split.
      -- exact (@measure_measurable_intersection R X alpha ha q.1 C hq1 hC).
      -- exact (@measure_measurable_difference R Y beta hb q.2 D hq2 hD).
  + move=> p q [[a haG <-]|[a haG <-]] [[b hbG <-]|[b hbG <-]] hne z hp hq.
    * have e := heq a b z haG hbG (hl a z hp) (hl b z hq).
      apply: hne; by rewrite e.
    * have e := heq a b z haG hbG (hl a z hp) (ht b z hq).
      exact: hp.1.2 hq.1.2.
    * have e := heq a b z haG hbG (ht a z hp) (hl b z hq).
      exact: hq.1.2 hp.1.2.
    * have e := heq a b z haG hbG (ht a z hp) (ht b z hq).
      apply: hne; by rewrite e.
  + apply/seteqP; split.
    * move=> [x y] [hs hn]; rewrite (disjoint_rectangle_union hg) in hs.
      have [p hp [hx hy]] := hs; case: (pselect (C x))=> hc.
      -- exists (T p); first by right; exists p.
         split; first by split.
         split=> //; move=> hd; apply: hn; by split.
      -- exists (L p); first by left; exists p.
         by split=> //; split.
    * move=> z [p [[q hq <-]|[q hq <-]] hp]; split.
      -- exact: (@disjoint_rectangle_cover_subset R X Y alpha beta G S hg q hq z (hl q z hp)).
      -- move=> hz; exact: hp.1.2 hz.1.
      -- exact: (@disjoint_rectangle_cover_subset R X Y alpha beta G S hg q hq z (ht q z hp)).
      -- move=> hz; exact: hp.2.2 hz.2.
Qed.
