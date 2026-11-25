(** The Euclidean Lebesgue-measure example in Federer (1969), 2.8.8, p. 145,
    referring to 2.7.16(1), pp. 134–135. We use the finite positive measure
    of the closed unit ball as a coefficient; proving it equals the
    open-ball coefficient is unnecessary for the growth estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology num_normedtype
  pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  InnerNormedTopology EuclideanCoordinateTopology EuclideanAdditiveGroup EuclideanLebesgue
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanLebesgueTranslation EuclideanLebesgueLinear
  EuclideanLebesgueDeterminant EuclideanLinearMaps MeasureUP MeasureBasic
  MetricClosedBalls BallPowerGrowth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section EuclideanGrowth.
Variable R : realType.
Variable n : nat.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Leb := (@euclidean_lebesgue_measure R n).

(** Source for [euclidean_metric_closed_ballE]: identification
    of the closed ball in the Euclidean example of Federer
    2.8.8, p. 145, with {|x-a|<=r}; the metric and
    norm agree by 1.7.1, p. 28. *)
Lemma euclidean_metric_closed_ballE (a : E) (r : R) :
  metric_closed_ball a r = [set x : E | `|x-a| <= r].
Proof.
by apply/seteqP; split=> x; rewrite /metric_closed_ball /= inner_metric_normE.
Qed.

(** Source for [euclidean_closed_unit_volume]: supporting
    closed-ball coefficient for the growth estimate in Federer
    2.8.8, p. 145, using the Lebesgue measure of 2.7.16.
    Only positivity and finiteness of this coefficient are needed. *)
Definition euclidean_closed_unit_volume : R := fine (Leb (metric_closed_ball (0 : E) 1)).

(** Source for [euclidean_closed_unit_volume_laws]: finite
    positive ball volume in the Euclidean example of Federer
    2.8.8, p. 145. The closed unit ball contains the
    positive-measure open unit ball and is compact. *)
Lemma euclidean_closed_unit_volume_laws :
  Leb (metric_closed_ball (0 : E) 1) = euclidean_closed_unit_volume%:E /\
    0 < euclidean_closed_unit_volume.
Proof.
have [hop _] := @euclidean_unit_ball_bounds R n.
have hsub : [set x : E | `|x| < 1] `<=` metric_closed_ball (0 : E) 1.
  move=> x hx; rewrite euclidean_metric_closed_ballE /= subr0; exact: ltW hx.
have hp := lt_le_trans hop (@measure_mono R E Leb (euclidean_lebesgue_is_measure R n) _ _ hsub).
have hf : (Leb (metric_closed_ball (0 : E)%R 1%R) < +oo)%E.
  rewrite euclidean_metric_closed_ballE.
  exact: euclidean_compact_finite (@euclidean_closed_ball_compact R n 0 1).
have hfin : Leb (metric_closed_ball (0 : E) 1) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative (euclidean_lebesgue_is_measure R n) _)); exact hf.
split; first by rewrite /euclidean_closed_unit_volume fineK.
by rewrite /euclidean_closed_unit_volume -lte_fin fineK.
Qed.

(** Source for [euclidean_closed_ball_measure]: the power growth in the
    Lebesgue example of Federer 2.8.8, p. 145, from translation and dilation
    in 2.7.16(1), pp. 134–135 Valid in dimension zero as well. *)
Theorem euclidean_closed_ball_measure (a : E) (r : R) : 0 < r ->
  Leb (metric_closed_ball a r) = (euclidean_closed_unit_volume * r ^+ n)%:E.
Proof.
move=> hr.
pose m := euclidean_diagonal_map (fun _ : 'I_n => r).
have hm (x : E) : (m : E -> E) x = r *: x.
  by apply/ffunP=> i; rewrite /m /= /euclidean_diagonal !ffunE.
have hdet : euclidean_det m = r ^+ n.
  by rewrite /m euclidean_diagonal_det prodr_const card_ord.
have himg : (m : E -> E) @` [set x : E | `|x| <= 1] = [set y : E | `|y| <= r].
  apply/seteqP; split=> y /=.
  - by move=> [x hx <-]; rewrite hm normrZ gtr0_norm // -{2}(mulr1 r) ler_pM2l.
  - move=> hy; exists (r^-1 *: y); last by rewrite hm scalerA mulfV ?scale1r //; exact: lt0r_neq0.
    rewrite /= normrZ gtr0_norm ?invr_gt0 // mulrC ler_pdivrMr // mul1r; exact hy.
have htr : [set x : E | `|x-a| <= r] = [set a+y | y in [set y : E | `|y| <= r]].
  apply/seteqP; split=> x /=.
  - by move=> hx; exists (x-a)=> //; rewrite addrC subrK.
  - by move=> [y hy <-]; rewrite addrC addKr.
rewrite euclidean_metric_closed_ballE htr euclidean_lebesgue_translation -himg
  euclidean_lebesgue_linear_image hdet.
have hu : [set x : E | `|x| <= 1] = metric_closed_ball (0 : E) 1.
  by rewrite euclidean_metric_closed_ballE; apply/seteqP; split=> x; rewrite /= subr0.
rewrite hu euclidean_closed_unit_volume_laws.1 -EFinM ger0_norm ?exprn_ge0 ?ltW //.
by rewrite mulrC.
Qed.

(** Source for [euclidean_closed_ball_power_growth]: the constants u=v equal
    to closed unit-ball volume establish the two-sided estimate in Federer's
    Euclidean example, 2.8.8, p. 145 They are independent of center and
    positive radius. *)
Theorem euclidean_closed_ball_power_growth (a : E) (s : R) : 0 < s ->
  has_ball_power_growth_bounds Leb n euclidean_closed_unit_volume
    euclidean_closed_unit_volume a s.
Proof.
move=> hs; rewrite /has_ball_power_growth_bounds (euclidean_closed_ball_measure a hs).
have hp : 0 < s ^+ n by rewrite exprn_gt0.
have hne : s ^+ n != 0 by rewrite (gt_eqF hp).
have he : (s ^+ n)^-1 * (euclidean_closed_unit_volume * s ^+ n) = euclidean_closed_unit_volume.
  by rewrite mulrCA mulVf // mulr1.
rewrite -EFinM he; by split.
Qed.
End EuclideanGrowth.
