(** Federer 2.10.2(1), p. 171, circle at a fixed cutoff. Supporting
    strict estimate alpha(2)>2 for the actual unit disc. An inscribed
    square has area two and a disjoint positive-radius ball also fits
    inside the disc. Every auxiliary square, centre and radius is local. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring num_normedtype.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerNormInequalities InnerMetric InnerNormedTopology
  EuclideanCoordinateMetric EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  EuclideanBallVolume RealMetricBackground MetricClosedBalls TopologicalBorel MeasureUP MeasureBasic MeasureFiniteAdditivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [planar_unit_disc_volume_gt_two]: Federer 2.10.2(1),
    p. 171; supporting scalar gap in the actual Euclidean circle's
    fixed-cutoff comparison. This elementary volume bound is expanded
    here and is not separately stated by Federer. *)
Lemma planar_unit_disc_volume_gt_two (R:realType):
  (2:R)<euclidean_unit_ball_volume R 2.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose N:=inner_norm (@euclidean_inner_productP R 2).
pose mu:=@euclidean_lebesgue_measure R 2.
pose a:=Num.sqrt (1/2:R).
have hHalf:(0<1/2:>R) by rewrite divr_gt0 // ltr0n.
have ha:0<a by rewrite /a sqrtr_gt0.
have ha2:a^+2=(1/2:R) := sqr_sqrtr (ltW hHalf).
have ha1:a<1 by nra.
pose b:=(a+1)/2.
have hab:a<b by rewrite /b; lra.
have hb1:b<1 by rewrite /b; lra.
have hb:0<b:=lt_trans ha hab.
pose eps:=Order.min ((b-a)/2) ((1-b)/2).
have heps:0<eps by rewrite /eps lt_min !divr_gt0 // !subr_gt0.
have hepsa:eps< b-a.
  have hmin:eps<=(b-a)/2 by rewrite /eps ge_min lexx.
  lra.
have heps1:b+eps<1.
  have hmin:eps<=(1-b)/2 by rewrite /eps ge_min lexx orbT.
  lra.
pose i1:'I_2:=@Ordinal 2 1 (erefl true).
pose center:X:=b*:(@coordinate_basis R 2 i1).
pose B:set X:=[set x|N x<1].
pose Q:set X:=[set x|forall i,-a<x i<a].
pose C:set X:=[set x|mdist center x<eps].
have hm:=euclidean_lebesgue_is_measure R 2.
have hB:mu B=(euclidean_unit_ball_volume R 2)%:E:=(euclidean_unit_ball_volumeE R 2).1.
have hQ:mu Q=(2:R)%:E.
  have hBound:-a<=a by lra.
  rewrite /mu /Q (@euclidean_open_box R 2 (fun _=>-a) (fun _=>a) (fun _=>hBound))
    prodr_const card_ord.
  congr (_%:E); nra.
have hC:mu C=(euclidean_unit_ball_volume R 2*eps^+2)%:E.
  have hEq:C=[set x : X | `|x-center| < eps].
    apply/seteqP; split=>x; by rewrite /C /= inner_metric_normE.
  rewrite hEq; exact:euclidean_ball_measure heps.
have hCM:measure_measurable mu C.
  apply:euclidean_borel_measurable; apply:open_borel_set; exact:metric_open_ball_open.
have hCenter:N center=b.
  rewrite /N /center inner_normZ euclidean_coordinate_unit_norm mulr1.
  exact:ger0_norm (ltW hb).
have hSquare x:(N x)^+2=(x ord0)^+2+(x i1)^+2.
  rewrite /N inner_norm_sqr /euclidean_inner_product !big_ord_recl big_ord0 !addr0 !expr2.
  have hIndex:(lift (ord0:'I_2) (ord0:'I_1)) = i1 by apply:val_inj.
  by rewrite hIndex.
have hQB:Q `<=` B.
  move=>x hx; have /andP[h0l h0u]:=hx ord0; have /andP[h1l h1u]:=hx i1.
  have hN:=inner_norm_nonnegative (@euclidean_inner_productP R 2) x.
  have hSq:=hSquare x; change (N x<1); nra.
have hCB:C `<=` B.
  move=>x hx.
  have hDist:N (x-center)<eps by move:hx; rewrite /C /= inner_metric_normE inner_norm_topologyE.
  have hT : N ((x-center)+center)<=N (x-center)+N center :=
    @inner_norm_triangle R (R_n R 2) (@euclidean_inner_product R 2)
      (@euclidean_inner_productP R 2) (x-center) center.
  rewrite subrK hCenter in hT.
  change (N x<1); lra.
have hDisjoint:forall x,C x ->Q x ->False.
  move=>x hx hqx.
  have hCenteri : center i1=b.
    rewrite /center /coordinate_basis !ffunE eqxx.
    change (b*1=b); exact:mulr1.
  have hCoord:=euclidean_coordinate_nonexpanding i1 center x.
  rewrite real_line_metric_distanceE hCenteri in hCoord.
  have hCx:`|b-x i1|<eps:=le_lt_trans hCoord hx.
  have hLow:=ler_norm (b-x i1).
  have /andP[_ hUpper]:=hqx i1.
  lra.
have hUnion:C `|` Q `<=` B by move=>x [hx|hx]; [exact:hCB x hx|exact:hQB x hx].
have hVolume:=@measure_mono R X mu hm _ _ hUnion.
rewrite (@measure_disjoint_union R X mu C Q hCM hDisjoint) hC hQ hB -EFinD lee_fin in hVolume.
have hPos:0<euclidean_unit_ball_volume R 2*eps^+2.
  apply:mulr_gt0; first exact:(euclidean_unit_ball_volumeE R 2).2.
  by rewrite exprn_gt0.
lra.
Qed.
