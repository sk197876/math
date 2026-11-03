(** Federer (1969), 3.2.43, printed p. 278, last
    proof sentence: finite lower codimension-one Minkowski
    content forces zero ambient volume. The proof uses all
    positive real radii and retains arbitrary original sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBallVolume MinkowskiContents MetricOpenThickening
  PositiveRadiusUnboundedValues ExtendedRealOrderTopology MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_volume_lower_codimension_content_infinite]:
    supporting contrapositive of the final observation in
    Federer 3.2.43, p. 278. Every positive ambient-volume
    source has infinite lower codimension-one content. No
    measurability, finite mass, boundedness or rectifiability
    hypothesis is added. *)
Lemma positive_volume_lower_codimension_content_infinite (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))):
  (0<@euclidean_lebesgue_measure R k.+1 S)%E ->
  lower_minkowski_content k S=+oo%E.
Proof.
move=>hPositive.
pose E:=inner_metric_space (@euclidean_inner_productP R k.+1).
pose mu:=@euclidean_lebesgue_measure R k.+1.
have hm:=euclidean_lebesgue_is_measure R k.+1.
have [q [hQ0 hQS]]:=@extended_rationals_order_dense R 0 (mu S) hPositive.
pose c:R:=ratr q.
have hc:0<c:=hQ0.
apply:positive_radius_lower_infinite_from_eventual_bounds=>b.
pose v:R:=`|b|+1.
have hv:0<v by rewrite /v ltr_wpDl ?normr_ge0.
have hTwo:0<(2:R) by rewrite ltr0n.
have hDen:0<2*v:=mulr_gt0 hTwo hv.
pose d:R:=c/(2*v).
have hd:0<d by rewrite /d divr_gt0.
exists d; split; first exact hd.
move=>r /andP[hr hrd].
have hRadius:r*(2*v)<c by move:hrd; rewrite /d ltr_pdivlMr.
have hBv:b<=v.
  apply:le_trans (ler_norm b) _.
  by rewrite /v lerDl ler01.
have hScalar:b*(2*r)<=c.
  apply:le_trans (ler_wpM2r (mulr_ge0 (ltW hTwo) (ltW hr)) hBv) _.
  apply:ltW; have hEq:v*(2*r)=r*(2*v) by ring.
  by rewrite hEq.
have hTube:(c%:E<=mu (metric_open_thickening S r))%E.
  apply:le_trans (ltW hQS) _.
  exact:(@measure_mono R E mu hm _ _ (@metric_open_thickening_includes R E S r hr)).
rewrite /minkowski_tube_quotient subSnn euclidean_unit_ball_volume1 expr1
  inver (gt_eqF (mulr_gt0 hTwo hr)).
rewrite (lee_pdivlMr _ _ (mulr_gt0 hTwo hr)) -EFinM.
have hScalarE:((b*(2*r))%:E<=c%:E)%E by rewrite lee_fin.
exact:(le_trans hScalarE hTube).
Qed.

(** Source for [finite_lower_codimension_content_ambient_null]:
    direct final observation in the proof of Federer
    3.2.43, p. 278, for the actual original source. In
    particular it applies to Bdry(S), independently of
    any rectifiability or boundary regularity. *)
Theorem finite_lower_codimension_content_ambient_null (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))):
  (lower_minkowski_content k S < +oo)%E ->
  @euclidean_lebesgue_measure R k.+1 S=0%E.
Proof.
move=>hFinite; apply:contrapT=>hNotZero.
have hPositive:(0<@euclidean_lebesgue_measure R k.+1 S)%E.
  rewrite lt_neqAle (measure_nonnegative (euclidean_lebesgue_is_measure R k.+1) S) andbT.
  apply/negP=>/eqP hZero; apply:hNotZero; exact:esym hZero.
have hInfinite:=positive_volume_lower_codimension_content_infinite hPositive.
by rewrite hInfinite ltxx in hFinite.
Qed.
