(** Federer (1969), 2.1.4, p. 56: measurable hulls and the finite-measure
    sufficient criterion. The local Federer erratum has no entry for this
    passage. *)
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

(** Source for [is_measure_hull]: Federer 2.1.4, p. 56, first paragraph and
    display; a measurable superset with equal intersection measures for
    every measurable test set. The measure laws are separate hypotheses. *)
Record is_measure_hull (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (A B : set I) : Prop := {
  measure_hull_subset : A `<=` B;
  measure_hull_measurable : measure_measurable mu B;
  measure_hull_test : forall T, measure_measurable mu T ->
    mu (T `&` A) = mu (T `&` B)
}.

(** Source for [measure_hull_equal_measure]: Federer 2.1.4, p. 56,
    supporting consequence of the defining test condition at X. *)
Lemma measure_hull_equal_measure (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (A B : set I) :
  is_measure_hull mu A B -> mu A = mu B.
Proof.
move=> h; have ht := measure_hull_test h (measure_measurable_whole hm).
by rewrite !setTI in ht.
Qed.

(** Source for [measure_hull_of_finite_equal_measure]: Federer 2.1.4, p. 56,
    second paragraph and display: a measurable superset of equal finite
    measure is a hull. The proof cancels the finite remainder after
    splitting by the measurable test; it retains the essential finiteness
    hypothesis. *)
Theorem measure_hull_of_finite_equal_measure (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (A B : set I) :
  A `<=` B -> measure_measurable mu B -> mu A = mu B -> mu A < +oo ->
  is_measure_hull mu A B.
Proof.
move=> hAB hB he hf; constructor=> // T hT.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@measure_mono R I mu hm _ _)=> x [ht ha]; split=> //; exact: hAB.
- have hd : A `\` T `<=` B `\` T.
    move=> x [ha ht]; split=> //; exact: hAB.
  have hfin : mu (A `\` T) \is a fin_num.
    rewrite ge0_fin_numE; last exact: (@measure_nonnegative R I mu hm).
    apply: le_lt_trans _ hf.
    apply: (@measure_mono R I mu hm _ _)=> x [hx _]; exact hx.
  have hsum := leeD2l (mu (T `&` B)) (measure_mono hm hd).
  have hAeq : mu A = mu (T `&` A) + mu (A `\` T).
    by rewrite (hT A) (setIC A T).
  have hBeq : mu B = mu (T `&` B) + mu (B `\` T).
    by rewrite (hT B) (setIC B T).
  by move: hsum; rewrite -hBeq -he hAeq leeD2rE.
Qed.
