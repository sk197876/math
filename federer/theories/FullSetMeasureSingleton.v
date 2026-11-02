(** Federer (1969), 2.1.5, p. 57, second irregular example: a three-point
    space with value one on nonempty proper subsets. the test-set argument
    is supplied here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FullSetMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [full_set_measure_contains_excludes]: Federer
    2.1.5, p. 57, supporting evaluation of a nonempty proper set
    using an included point and an excluded point. *)
Lemma full_set_measure_contains_excludes (R : realType) (I : choiceType)
    (A : set I) (x y : I) : A x -> ~ A y -> full_set_measure (R := R) A = (1 : R)%:E.
Proof.
move=> hx hy; apply: full_set_measure_proper.
- by apply/eqP=> he; rewrite he in hx.
- apply/eqP=> he; apply: hy; by rewrite he.
Qed.

(** Source for [full_set_measure_singleton_not_measurable]: Federer
    2.1.5, p. 57, supporting failure of measurability for the second
    example. Three distinct points suffice: a two-point test has value
    one but splits into two singletons of value one. *)
Lemma full_set_measure_singleton_not_measurable (R : realType) (I : choiceType)
    (a b c : I) : a != b -> a != c -> b != c ->
  ~ measure_measurable (@full_set_measure R I) [set a].
Proof.
move=> hab hac hbc hm.
pose T := [set a] `|` [set b].
have hT : full_set_measure (R := R) T = (1 : R)%:E.
  apply: (@full_set_measure_contains_excludes R I T a c); first by left.
  move=> [he|he]; [by move: hac; rewrite he eqxx | by move: hbc; rewrite he eqxx].
have hA : full_set_measure (R := R) [set a] = (1 : R)%:E.
  apply: (@full_set_measure_contains_excludes R I [set a] a b)=> //.
  by move=> he; move: hab; rewrite he eqxx.
have hB : full_set_measure (R := R) [set b] = (1 : R)%:E.
  apply: (@full_set_measure_contains_excludes R I [set b] b a)=> //.
  by move=> he; move: hab; rewrite he eqxx.
have hi : T `&` [set a] = [set a].
  apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; by left.
have hd : T `\` [set a] = [set b].
  apply/seteqP; split.
  - move=> x [[ha|hb] hn] //; exfalso; exact: hn ha.
  - move=> x hb; split; first by right.
    move=> ha; have he : a = b by rewrite -ha hb.
    by move: hab; rewrite he eqxx.
have he := hm T; rewrite hi hd hT hA hB in he.
have hlt : (1 : \bar R) < 1 + 1 by rewrite -EFinD lte_fin ltrDl ltr01.
by rewrite -he ltxx in hlt.
Qed.
