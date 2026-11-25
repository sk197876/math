(** Federer (1969), 2.1.5, p. 57, final paragraph: regularisation is a
    regular measure, agrees on originally measurable sets, and adds no
    finite-measure measurable sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport
  MeasureUP MeasureBasic MeasureSplit MeasureIndexedCover MeasureFiniteClosure
  MeasureCountableClosure RegularMeasureUP MeasureRegularisationUP
  MeasureRegularisationBasic MeasureRegularisationAttainment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_regularisation_is_measure]: Federer 2.1.5, p. 57,
    regularisation is a measure. Choose attaining measurable supersets and
    apply the old measure's covering inequality to their countable union. *)
Theorem measure_regularisation_is_measure (R : realType) (I : choiceType)
    (mu nu : set I -> \bar R) (hm : is_measure mu)
    (hr : is_measure_regularisation mu nu) : is_measure nu.
Proof.
constructor; first by move=> A; exact: (@measure_regularisation_nonnegative R I mu nu hm hr A).
move=> A F hF hc.
pose B C := projT1 (cid (@measure_regularisation_attained R I mu nu hm hr C)).
have hB C : C `<=` B C /\ measure_measurable mu (B C) /\ nu C = mu (B C).
  exact: projT2 (cid (@measure_regularisation_attained R I mu nu hm hr C)).
have hU : measure_measurable mu (\bigcup_(C in F) B C).
  apply: (@measure_measurable_countable_union R I _ mu hm F B hF)=> C _.
  exact: (hB C).2.1.
have hcover : A `<=` \bigcup_(C in F) B C.
  move=> x hx; have [C hC hxC] := hc x hx; exists C=> //; exact: (hB C).1.
apply: le_trans (@measure_regularisation_lower R I mu nu hr A _ hcover hU) _.
have hb := @measure_indexed_cover R I _ mu hm (\bigcup_(C in F) B C) F B hF
  (fun x hx => hx).
have he : nonnegative_sum F (fun C => mu (B C)) = nonnegative_sum F nu.
  apply: nonnegative_sum_ext=> C _; exact: esym (hB C).2.2.
by rewrite he in hb.
Qed.

(** Source for [measure_regularisation_preserves_measurable]: Federer 2.1.5,
    p. 57; every originally measurable set remains measurable for the
    regularisation. *)
Theorem measure_regularisation_preserves_measurable (R : realType) (I : choiceType)
    (mu nu : set I -> \bar R) (hm : is_measure mu)
    (hr : is_measure_regularisation mu nu) A :
  measure_measurable mu A -> measure_measurable nu A.
Proof.
move=> hA T; have hn := @measure_regularisation_is_measure R I mu nu hm hr.
apply/eqP; rewrite eq_le (measure_split_upper hn) /=.
have [B [hTB [hB he]]] := @measure_regularisation_attained R I mu nu hm hr T.
rewrite he (hA B); apply: leeD.
- apply: (@measure_regularisation_lower R I mu nu hr (T `&` A) (B `&` A)).
  + move=> x [ht ha]; split=> //; exact: hTB.
  + exact: (@measure_measurable_intersection R I mu hm B A hB hA).
- apply: (@measure_regularisation_lower R I mu nu hr (T `\` A) (B `\` A)).
  + move=> x [ht ha]; split=> //; exact: hTB.
  + exact: (@measure_measurable_difference R I mu hm B A hB hA).
Qed.

(** Source for [measure_regularisation_regular]: Federer 2.1.5, p. 57, the
    constructed measure is regular. The attaining old-measurable superset is
    also measurable for the new measure and has unchanged value. *)
Theorem measure_regularisation_regular (R : realType) (I : choiceType)
    (mu nu : set I -> \bar R) (hm : is_measure mu)
    (hr : is_measure_regularisation mu nu) : is_regular_measure nu.
Proof.
move=> A; have [B [hAB [hB he]]] := @measure_regularisation_attained R I mu nu hm hr A.
exists B; split=> //; split.
- exact: (@measure_regularisation_preserves_measurable R I mu nu hm hr B hB).
- by rewrite (@measure_regularisation_measurable_value R I mu nu hm hr B hB).
Qed.

(** Source for [measure_regularisation_finite_measurable_back]: Federer
    2.1.5, p. 57, final sentence: a newly measurable set of finite new
    measure was already measurable for the old measure. *)
Theorem measure_regularisation_finite_measurable_back (R : realType) (I : choiceType)
    (mu nu : set I -> \bar R) (hm : is_measure mu)
    (hr : is_measure_regularisation mu nu) A :
  measure_measurable nu A -> nu A < +oo -> measure_measurable mu A.
Proof.
move=> hA hf; have [B [hAB [hB he]]] := @measure_regularisation_attained R I mu nu hm hr A.
have hv : nu B = nu A.
  by rewrite (@measure_regularisation_measurable_value R I mu nu hm hr B hB) -he.
have hfin : nu A \is a fin_num.
  by rewrite ge0_fin_numE //; exact: (@measure_regularisation_nonnegative R I mu nu hm hr A).
have hzero : nu (B `\` A) = 0.
  have hi : B `&` A = A.
    apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hAB.
  have h := hA B; rewrite hi hv in h.
  have hcancel := congr1 (fun t => t - nu A) h.
  by rewrite subee // (addeC (nu A) (nu (B `\` A))) addeK // in hcancel.
have hnull : mu (B `\` A) = 0.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  have h := @measure_regularisation_dominates R I mu nu hm hr (B `\` A).
  by rewrite hzero in h.
have hN := @measure_null_measurable R I mu hm (B `\` A) hnull.
have hmA := @measure_measurable_difference R I mu hm B (B `\` A) hB hN.
have hEq : B `\` (B `\` A) = A.
  apply/seteqP; split.
  - move=> x [hb hn]; case: (pselect (A x))=> ha //.
    exfalso; apply: hn; by split.
  - move=> x ha; split; first exact: hAB.
    by move=> [_ hn]; exact: hn.
by rewrite hEq in hmA.
Qed.
