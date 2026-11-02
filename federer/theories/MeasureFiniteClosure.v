(** Federer (1969), 2.1.3(1),(2),(6), pp. 54-56: finite closure and null-set
    measurability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_measurable_complement]: Federer 2.1.3(1), p. 54;
    complements preserve measurability by interchanging the two test-set
    pieces. *)
Lemma measure_measurable_complement (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (A : set I) :
  measure_measurable mu A -> measure_measurable mu (~` A).
Proof.
move=> h T; rewrite !setDE setCK addeC; exact: h.
Qed.

(** Source for [measure_measurable_union]: Federer 2.1.3, p. 55, first
    paragraph of proof of (2): split first by A, then split the remainder by
    B, and apply subadditivity. Supporting finite-union case *)
Lemma measure_measurable_union (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (A B : set I) :
  measure_measurable mu A -> measure_measurable mu B ->
  measure_measurable mu (A `|` B).
Proof.
move=> hA hB T; apply/eqP; rewrite eq_le (measure_split_upper hm) /=.
have hd : (T `\` A) `\` B = T `\` (A `|` B).
  by rewrite !setDE setCU setIA.
have hc : T `&` (A `|` B) `<=` (T `&` A) `|` ((T `\` A) `&` B).
  move=> x [ht hab]; case: (pselect (A x))=> ha; first by left; split.
  right; split; first by split.
  by case: hab=> // hax; contradiction.
rewrite (hA T) (hB (T `\` A)) addeA hd.
apply: leeD; last exact: lexx.
exact: (@measure_binary_cover R I mu hm _ _ _ hc).
Qed.

(** Source for [measure_measurable_intersection]: Federer 2.1.3(2), p. 55,
    finite-family part of the proof; intersection follows from union and
    complement. *)
Lemma measure_measurable_intersection (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (A B : set I) :
  measure_measurable mu A -> measure_measurable mu B ->
  measure_measurable mu (A `&` B).
Proof.
move=> hA hB.
have hu := @measure_measurable_union R I mu hm (~` A) (~` B)
  (measure_measurable_complement hA) (measure_measurable_complement hB).
have hc := measure_measurable_complement hu.
by rewrite setCU !setCK in hc.
Qed.

(** Source for [measure_measurable_difference]: Federer
    2.1.3, p. 55, difference sets used in the proof of (4);
    supporting closure consequence of (1) and finite (2). *)
Lemma measure_measurable_difference (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (A B : set I) :
  measure_measurable mu A -> measure_measurable mu B ->
  measure_measurable mu (A `\` B).
Proof.
move=> hA hB; exact: (@measure_measurable_intersection R I mu hm A (~` B)
  hA (measure_measurable_complement hB)).
Qed.

(** Source for [measure_null_measurable]: Federer 2.1.3(6), p. 55;
    zero-measure sets satisfy the splitting condition. *)
Lemma measure_null_measurable (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (A : set I) :
  mu A = 0 -> measure_measurable mu A.
Proof.
move=> hA T; apply/eqP; rewrite eq_le (measure_split_upper hm) /=.
have h0 : mu (T `&` A) = 0.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT -hA.
  by apply: (@measure_mono R I mu hm _ _)=> x [].
rewrite h0 add0e; apply: (@measure_mono R I mu hm _ _)=> x [hx _]; exact hx.
Qed.
