(** Federer (1969), 3.2.43, printed p. 278:
    the lower codimension-one Minkowski content of the
    original boundary bounds the printed power of the
    finite original closure volume. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBallVolume RealPower MinkowskiContents MinkowskiContentsBasic
  CodimensionOneFiniteContentNull PositiveVolumeIsoperimetric MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_closure_volume_isoperimetric]: direct
    positive finite-volume case of Federer 3.2.43, p. 278,
    in every positive ambient dimension, including one.
    Infinite lower boundary content is immediate; finite
    content proves ambient boundary nullity and discharges
    that premise of the actual two-strip proof. *)
Theorem positive_closure_volume_isoperimetric (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))) (a:R):
  @euclidean_lebesgue_measure R k.+1 (closure S)=a%:E ->0<a ->
  (((k.+1)%:R*real_power (euclidean_unit_ball_volume R k.+1) ((k.+1)%:R)^-1*
    real_power a (k%:R/(k.+1)%:R))%:E<=
      lower_minkowski_content k (closure S `\` interior S))%E.
Proof.
move=>hMass ha.
pose B:=closure S `\` interior S.
case hValue:(lower_minkowski_content k B)=>[v| |].
- have hFinite:(lower_minkowski_content k B < +oo)%E by rewrite hValue ltry.
  have hNull:=finite_lower_codimension_content_ambient_null hFinite.
  have h:=positive_volume_null_boundary_isoperimetric hMass ha hNull.
  by rewrite /B in hValue; rewrite hValue in h.
- exact:leey.
- have hNonnegative:=(@minkowski_contents_nonnegative R k.+1 k B).1.
  by rewrite hValue leNgt ltNyr in hNonnegative.
Qed.

(** Source for [federer_3_2_43]: direct isoperimetric inequality,
    Federer 3.2.43, p. 278, in ambient dimensions at least
    two. Every original source with finite closure volume
    is retained, without measurability, boundedness or boundary
    rectifiability hypotheses. The zero-volume case has a
    positive exponent and is included. The positive-volume
    line case is supplied separately, with its actual exponent
    zero; a zero-volume singleton precludes a blanket extension. *)
Theorem federer_3_2_43 (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+2))):
  (@euclidean_lebesgue_measure R k.+2 (closure S) < +oo)%E ->
  (((k.+2)%:R*real_power (euclidean_unit_ball_volume R k.+2) ((k.+2)%:R)^-1*
    real_power (fine (@euclidean_lebesgue_measure R k.+2 (closure S)))
      ((k.+1)%:R/(k.+2)%:R))%:E<=
      lower_minkowski_content k.+1 (closure S `\` interior S))%E.
Proof.
move=>hFinite.
pose mu:=@euclidean_lebesgue_measure R k.+2.
have hm:=euclidean_lebesgue_is_measure R k.+2.
have hFin:mu (closure S) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)); exact hFinite.
pose a:R:=fine (mu (closure S)).
have hMass:mu (closure S)=a%:E by rewrite /a fineK.
have ha:0<=a.
  have h:(0<=mu (closure S))%E:=measure_nonnegative hm _.
  by rewrite hMass lee_fin in h.
case:(eqVneq a 0)=>[ha0|ha0].
- have hp:0<((k.+1)%:R/(k.+2)%:R:R) by rewrite divr_gt0 ?ltr0n.
  have hpNe:((k.+1)%:R/(k.+2)%:R:R)!=0 by rewrite (gt_eqF hp).
  change (is_true (((k.+2)%:R*real_power (euclidean_unit_ball_volume R k.+2) ((k.+2)%:R)^-1*
    real_power a ((k.+1)%:R/(k.+2)%:R))%:E<=
      lower_minkowski_content k.+1 (closure S `\` interior S))%E).
  rewrite ha0 (real_power_zero_base hpNe) mulr0.
  exact:(@minkowski_contents_nonnegative R k.+2 k.+1 _).1.
- have hPos:0<a by rewrite lt_neqAle eq_sym ha0 ha.
  exact:(@positive_closure_volume_isoperimetric R k.+1 S a hMass hPos).
Qed.
