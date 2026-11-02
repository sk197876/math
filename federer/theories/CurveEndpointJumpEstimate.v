(** Supporting the lower estimate in Federer (1969), 2.10.14, p. 177:
    endpoint distance is bounded by the H1 image measure plus the two
    one-sided jump budgets. Apply Lebesgue measure to the oriented bridge
    cover. Finite numerical budgets give countable positive supports by
    2.1.1(12), p. 53. They do not state this jump estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CurveOneSidedJumpUP CurveJumpBridgeCover
  NonnegativeSum NonnegativeSumSupport NonnegativeSumCountable
  MeasureUP MeasureBasic MeasureSplit MeasureIndexedCover LebesgueScalarMeasure
  HausdorffLength HausdorffLengthMaps HausdorffLengthReal ConnectedHausdorffLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_weight_positive_support_countable]: supporting
    countability of the jump bridges in 2.10.14, p. 177, from the
    numerical-sum theorem 2.1.1(12), p. 53 *)
Lemma real_weight_positive_support_countable (R : realType) (X : choiceType)
    (A : set X) (w : X -> R) : (forall x, A x -> (0<=w x)%R) ->
  nonnegative_sum A (fun x => (w x)%:E)< +oo ->
  countable (A `&` [set x | (0<w x)%R]).
Proof.
move=> hw hs.
have hpos x : A x -> 0<=(w x)%:E by move=> hx; rewrite lee_fin; exact: hw x hx.
have hc := @nonnegative_sum_countable_support R X A (fun x => (w x)%:E) hpos hs.
apply: sub_countable _ hc; apply: subset_card_le=> x [hx hp]; split=> //.
apply/eqP=> he; have hE : 0<(w x)%:E by rewrite lte_fin.
by rewrite he ltxx in hE.
Qed.

(** Source for [distance_projection_image_length_bound]: supporting
    distance-map comparison in 2.10.14, p. 177, using
    the same map as 2.10.12, p. 176. Its scalar image
    has Lebesgue measure at most the H1 measure of the
    curve image, without any source measurability premise. *)
Lemma distance_projection_image_length_bound (R : realType) (X : choiceType)
    (Y : metricType R) (g : X -> Y) (a : Y) (A : set X) :
  @lebesgue_scalar_measure R ((fun x => (mdist a (g x) : real_line_metric R)) @` A)
    <=@hausdorff_length R Y (g @` A).
Proof.
pose F (y : Y) : real_line_metric R := mdist a y.
have he : (fun x => (mdist a (g x) : real_line_metric R)) @` A=F @` (g @` A).
  apply/seteqP; split=> y.
  - move=> [x hx <-]; exists (g x); first by exists x.
    by [].
  - move=> [z [x hx <-] <-]; by exists x.
rewrite he -(@hausdorff_length_real_eq_lebesgue R).
exact: (@hausdorff_length_nonexpanding R Y [the metricType R of real_line_metric R]
  F (@distance_from_point_nonexpanding R Y a) (g @` A)).
Qed.

(** Source for [curve_endpoint_real_jump_budget_bound]: supporting
    endpoint estimate for 2.10.14, p. 177. Real nonnegative
    bounds on the two upper-limit jumps give oriented bridge
    lengths. Finite budgets make their supports countable; the
    curve itself may be discontinuous and have infinite variation. *)
Theorem curve_endpoint_real_jump_budget_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (r l : R -> R) (a b : R) : (a<b)%R ->
  (forall x, (a<=x<b)%R -> (0<=r x)%R) ->
  (forall x, (a<x<=b)%R -> (0<=l x)%R) ->
  (forall x, (a<=x<b)%R -> curve_right_jump_size g x<=(r x)%:E) ->
  (forall x, (a<x<=b)%R -> curve_left_jump_size g x<=(l x)%:E) ->
  nonnegative_sum (`[a,b[ : set (real_line_metric R)) (fun x => (r x)%:E)< +oo ->
  nonnegative_sum (`]a,b] : set (real_line_metric R)) (fun x => (l x)%:E)< +oo ->
  (mdist (g a) (g b))%:E<=@hausdorff_length R Y (g @` `[a,b])+
    nonnegative_sum (`[a,b[ : set (real_line_metric R)) (fun x => (r x)%:E)+
    nonnegative_sum (`]a,b] : set (real_line_metric R)) (fun x => (l x)%:E).
Proof.
move=> hab hr0 hl0 hr hl hR hL.
pose f (t : R) : R := mdist (g a) (g t).
pose DR := [set x : real_line_metric R | (a<=x<b)%R /\ (0<r x)%R].
pose DL := [set x : real_line_metric R | (a<x<=b)%R /\ (0<l x)%R].
pose UR := \bigcup_(x in DR) right_curve_jump_bridge f r x.
pose UL := \bigcup_(x in DL) left_curve_jump_bridge f l x.
have hDR : countable DR.
  exact: (@real_weight_positive_support_countable R [the choiceType of real_line_metric R]
    `[a,b[ r (fun x hx => hr0 x hx) hR).
have hDL : countable DL.
  exact: (@real_weight_positive_support_countable R [the choiceType of real_line_metric R]
    `]a,b] l (fun x hx => hl0 x hx) hL).
have hf t u : (f t-f u<=mdist (g t) (g u))%R.
  have hh := metric_triangle (g a) (g u) (g t).
  rewrite (metric_sym (g u) (g t)) in hh.
  rewrite /f; lra.
have hcover := @curve_jump_bridge_cover R Y g f r l a b hab hf hr hl.
rewrite /f mdistxx in hcover.
have hM := lebesgue_scalar_is_measure R.
have hRU : lebesgue_scalar_measure UR<=nonnegative_sum (`[a,b[ : set (real_line_metric R)) (fun x => (r x)%:E).
  have hh := @measure_indexed_cover R [the choiceType of real_line_metric R]
    [the choiceType of real_line_metric R] (@lebesgue_scalar_measure R) hM UR DR
    (right_curve_jump_bridge f r) hDR (fun x hx => hx).
  have he : nonnegative_sum DR (fun x => lebesgue_scalar_measure (right_curve_jump_bridge f r x))=
      nonnegative_sum DR (fun x => (r x)%:E).
    apply: nonnegative_sum_ext=> x [hx hp].
    have horder : (f x<=f x+r x)%R by lra.
    rewrite /right_curve_jump_bridge (@lebesgue_scalar_segment R (f x) (f x+r x)%R horder).
    have heq : (f x+r x-f x=r x)%R by lra.
    by rewrite heq.
  rewrite he in hh; apply: le_trans hh _.
  apply: nonnegative_sum_subset=> x [hx _]; exact hx.
have hLU : lebesgue_scalar_measure UL<=nonnegative_sum (`]a,b] : set (real_line_metric R)) (fun x => (l x)%:E).
  have hh := @measure_indexed_cover R [the choiceType of real_line_metric R]
    [the choiceType of real_line_metric R] (@lebesgue_scalar_measure R) hM UL DL
    (left_curve_jump_bridge f l) hDL (fun x hx => hx).
  have he : nonnegative_sum DL (fun x => lebesgue_scalar_measure (left_curve_jump_bridge f l x))=
      nonnegative_sum DL (fun x => (l x)%:E).
    apply: nonnegative_sum_ext=> x [hx hp].
    have horder : (f x-l x<=f x)%R by lra.
    rewrite /left_curve_jump_bridge (@lebesgue_scalar_segment R (f x-l x)%R (f x) horder).
    have heq : (f x-(f x-l x)=l x)%R by lra.
    by rewrite heq.
  rewrite he in hh; apply: le_trans hh _.
  apply: nonnegative_sum_subset=> x [hx _]; exact hx.
have hbound := measure_binary_cover hM hcover.
rewrite lebesgue_scalar_segment ?mdist_ge0 // subr0 in hbound.
have hUnion : lebesgue_scalar_measure (UR `|` UL)<=lebesgue_scalar_measure UR+lebesgue_scalar_measure UL.
  exact: (@measure_binary_cover R [the choiceType of real_line_metric R]
    (@lebesgue_scalar_measure R) hM (UR `|` UL) UR UL (fun x hx => hx)).
apply: le_trans hbound _.
apply: le_trans (leeD (lexx _) hUnion) _.
rewrite -addeA; apply: leeD; last exact: leeD hRU hLU.
exact: (@distance_projection_image_length_bound R [the choiceType of real_line_metric R] Y g (g a) `[a,b]).
Qed.
