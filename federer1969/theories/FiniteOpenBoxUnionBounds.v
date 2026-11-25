(** Federer (1969), 3.2.41, printed p. 277: actual
    finite box unions have finite volume, and a nonempty one
    has positive volume. Positive cut mass supplies the genuine
    nonempty sets required by the smaller-family induction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric GrassmannAbbreviations
  EuclideanLebesgueDimensions FiniteDisjointOpenBoxFamilyUP FiniteDisjointOpenBoxVolume
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.

(** Source for [positive_measure_set_nonempty]: supporting
    nonemptiness from actual positive cut volume in Federer
    3.2.41, p. 277. Only the empty-set measure law is used;
    the source may be nonmeasurable and have infinite mass. *)
Lemma positive_measure_set_nonempty (R:realType) (X:choiceType)
    (mu:set X->\bar R) (S:set X):
  is_measure mu ->(0<mu S)%E ->S !=set0.
Proof.
move=> hm hPos; apply:contrapT=> hEmpty.
have hSet:S=set0.
  apply/seteqP; split; last by move=> x [].
  move=> x hx; apply:hEmpty; by exists x.
by rewrite hSet (measure_empty hm) ltxx in hPos.
Qed.

(** Source for [finite_open_box_union_finite_volume]: supporting
    proved finite normalization in Federer 3.2.41, p. 277,
    including an empty finite family of boxes. *)
Lemma finite_open_box_union_finite_volume (R:realType) n (I:finType)
    (a b:I->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n))):
  is_finite_disjoint_open_box_family a b G ->
  (@euclidean_lebesgue_measure R n (\bigcup_i G i) < +oo)%E.
Proof.
move=> hG; rewrite (finite_disjoint_open_box_union_volume hG); exact:ltry.
Qed.

(** Source for [finite_open_box_union_positive_volume]: supporting
    proved strict normalization in Federer 3.2.41, p. 277.
    The original nonempty union supplies an actual family index. *)
Lemma finite_open_box_union_positive_volume (R:realType) n (I:finType)
    (a b:I->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n))):
  is_finite_disjoint_open_box_family a b G ->(\bigcup_i G i) !=set0 ->
  (0<@euclidean_lebesgue_measure R n (\bigcup_i G i))%E.
Proof.
move=> hG [x [i _ hi]].
exact:(andP (@finite_disjoint_open_box_union_positive_finite R n I a b G i hG)).1.
Qed.
