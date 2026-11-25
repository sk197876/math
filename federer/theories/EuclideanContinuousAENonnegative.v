(** Federer (1969), 4.1.14, pp. 371–372: the continuous
    almost-everywhere derivative majorant is nonnegative at every
    point of its open domain. This supporting consequence follows
    from the positive measure of nonempty open Euclidean sets,
    2.7.16, pp. 134–135, including dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric NormClassOneUP NormClassZeroTopology
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext CoveringFamilyUP MetricClosedBalls
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_continuous_ae_nonnegative]: the
    nonnegativity implicit in the continuous sigma of Federer
    4.1.14, p. 371. It is a conclusion, not an extra premise on
    the original majorant. The empty domain is allowed. *)
Theorem euclidean_continuous_ae_nonnegative (R:realType) n
    (U:set (R_n R n)) (sigma:R_n R n->R^o):
  norm_class_zero (inner_norm (@euclidean_inner_productP R n))
    (fun t:R^o=>`|t|) U sigma ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set x|U x->0<=sigma x] ->forall x,U x->0<=sigma x.
Proof.
move=>hContinuous hAE a ha.
apply/negPn/negP=>hBad.
have hNegative:sigma a<0 by rewrite ltNge.
pose eta:= -sigma a/2.
have hEta:0<eta by rewrite /eta divr_gt0 //;lra.
have[r [hr hControl]]:=@norm_class_zero_local_control R (R_n R n) R^o
  (inner_norm (@euclidean_inner_productP R n)) (fun t:R^o=>`|t|)
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U sigma a eta
  hContinuous ha hEta.
pose T:=real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)).
pose B:=@metric_open_ball R T a r.
have hBa:B a.
  change (is_true (inner_norm (@euclidean_inner_productP R n) (a-a)<r)).
  by rewrite subrr (real_seminorm_zero
    (inner_norm_real_norm (@euclidean_inner_productP R n)).1).
have hPositive:(0<@euclidean_lebesgue_measure R n B)%E:=
  @euclidean_distribution_measure_open_positive R n B a
    (@metric_open_ball_open R T a r) hBa.
have hNull:@euclidean_lebesgue_measure R n B=0.
  apply:(@measure_null_subset R (R_n R n) (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) B (~`[set x|U x->0<=sigma x]) _ hAE).
  move=>x hx hGood.
  have hNear:inner_norm (@euclidean_inner_productP R n) (x-a)<r.
    change (is_true (inner_norm (@euclidean_inner_productP R n) (a-x)<r)) in hx.
    by rewrite (real_seminorm_subtract
      (inner_norm_real_norm (@euclidean_inner_productP R n)).1).
  have[hUx hDifference]:=hControl x hNear.
  have hNonnegative:=hGood hUx.
  have hBelow:=ler_norm (sigma x-sigma a).
  rewrite /eta in hDifference;nra.
by rewrite hNull ltxx in hPositive.
Qed.
