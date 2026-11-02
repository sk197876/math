(** Federer (1969), 2.1.6, p. 58: replacing a disjoint family by an index
    space, with measure of an index set equal to the measure of the
    corresponding union. This supports the equivalence of the two
    Ulam-number definitions. Source context and absence of a corresponding. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureIndexedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.
Local Open Scope ereal_scope.

(** Source for [measure_family_union]: Federer 2.1.6, p. 58,
    supporting indexed notation for the union of a subfamily. D is
    the full index set; A selects a subfamily. Empty or repeated
    empty members are allowed. *)
Definition measure_family_union (I J : choiceType) (D : set J)
    (F : J -> set I) (A : set J) := \bigcup_(j in D `&` A) F j.

(** Source for [measure_family_image]: Federer 2.1.6, p. 58,
    second-to-first direction: phi(G) = psi(union G). This is the
    indexed version, on all subsets of the ambient index type. *)
Definition measure_family_image (R : realType) (I J : choiceType)
    (mu : set I -> \bar R) (D : set J) (F : J -> set I) :=
  fun A => mu (measure_family_union D F A).

(** Source for [measure_family_image_is_measure]: Federer
    2.1.6, p. 58, supporting verification that the induced function
    is a measure. The covering inequality holds even without disjointness. *)
Lemma measure_family_image_is_measure (R : realType) (I J : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (D : set J) (F : J -> set I) :
  is_measure (measure_family_image mu D F).
Proof.
constructor; first by move=> A; exact: (measure_nonnegative hm).
move=> A G hG hc; apply: (@measure_indexed_cover R I _ mu hm _ G
  (measure_family_union D F) hG).
move=> x [j [hj ha] hx].
have [B hb hjb] := hc j ha; exists B=> //; exists j=> //; by split.
Qed.

(** Source for [measure_family_union_full]: Federer 2.1.6,
    p. 58, supporting identity identifying the total induced measure
    with the measure of the full union. *)
Lemma measure_family_union_full (I J : choiceType) (D : set J) (F : J -> set I) :
  measure_family_union D F D = \bigcup_(j in D) F j.
Proof. by rewrite /measure_family_union setIid. Qed.

(** Source for [measure_family_union_singleton]: Federer
    2.1.6, p. 58: the induced measure of an index singleton is
    the original measure of that member of the family. *)
Lemma measure_family_union_singleton (I J : choiceType) (D : set J)
    (F : J -> set I) j : D j -> measure_family_union D F [set j] = F j.
Proof.
move=> hj; apply/seteqP; split.
- by move=> x [k [_ ->] hx].
- move=> x hx; exists j=> //; by split.
Qed.

(** Source for [measure_family_union_intersection]: Federer
    2.1.6, p. 58, supporting set identity: disjointness makes
    union of subfamilies preserve intersection. *)
Lemma measure_family_union_intersection (I J : choiceType) (D : set J)
    (F : J -> set I) :
  (forall j k, D j -> D k -> j <> k -> F j `&` F k = set0) ->
  forall A B, measure_family_union D F (A `&` B) =
    measure_family_union D F A `&` measure_family_union D F B.
Proof.
move=> hd A B; apply/seteqP; split.
- move=> x [j [hj [ha hb]] hx]; split; exists j=> //; by split.
- move=> x [[j [hj ha] hxj] [k [hk hb] hxk]].
  have he : j = k.
    apply: contrapT=> hn; have hx : (F j `&` F k) x by split.
    by rewrite (hd j k hj hk hn) in hx.
  exists j; last exact hxj.
  by split=> //; split=> //; rewrite he.
Qed.

(** Source for [measure_family_union_difference]: Federer
    2.1.6, p. 58, supporting set identity: disjointness makes
    union of subfamilies preserve relative difference. *)
Lemma measure_family_union_difference (I J : choiceType) (D : set J)
    (F : J -> set I) :
  (forall j k, D j -> D k -> j <> k -> F j `&` F k = set0) ->
  forall A B, measure_family_union D F (A `\` B) =
    measure_family_union D F A `\` measure_family_union D F B.
Proof.
move=> hd A B; apply/seteqP; split.
- move=> x [j [hj [ha hn]] hx]; split.
  + exists j=> //; by split.
  + move=> [k [hk hb] hxk].
    have he : j = k.
      apply: contrapT=> hne; have ht : (F j `&` F k) x by split.
      by rewrite (hd j k hj hk hne) in ht.
    apply: hn; by rewrite he.
- move=> x [[j [hj ha] hx] hn]; exists j=> //; split=> //; split=> //.
  move=> hb; apply: hn; exists j=> //; by split.
Qed.

(** Source for [measure_family_image_all_measurable]: Federer
    2.1.6, p. 58, verification of the induced measure's defining
    hypothesis: all index subsets are measurable if all subfamily
    unions are originally measurable and the family is disjoint. *)
Lemma measure_family_image_all_measurable (R : realType) (I J : choiceType)
    (mu : set I -> \bar R) (D : set J) (F : J -> set I) :
  (forall j k, D j -> D k -> j <> k -> F j `&` F k = set0) ->
  (forall A, measure_measurable mu (measure_family_union D F A)) ->
  forall A, measure_measurable (measure_family_image mu D F) A.
Proof.
move=> hd hm A T; rewrite /measure_family_image
  (measure_family_union_intersection hd) (measure_family_union_difference hd).
exact: hm.
Qed.
