(** Federer (1969), 3.2.33, p. 270: finite global
    bounds for each actual derivative of the compactly supported
    smooth function phi, supporting the printed series. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology num_normedtype normedtype.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground NormMetricScaleContinuity
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialUnique
  NormClassOneUP NormClassHigherUP NormRegularity NormCompactSupportHigherBound PositiveUnitIntervalBumpUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_interval_bump_differential_bounds]: supporting
    convergence of every differentiated series in Federer 3.2.33,
    p. 270. Compact support supplies finite bounds through
    3.1.13, p. 224. Every supplied field is an actual
    continuous higher differential on the entire scalar line;
    its values outside [0,1] are zero by locality. The fields
    and bounds are local existential data, not extra hypotheses
    or new globally chosen objects. *)
Theorem positive_interval_bump_differential_bounds (R:realType) (phi:R->R):
  is_positive_unit_interval_bump phi ->
  let N:=fun t:R^o=>`|t| in
  let hN:=scalar_absolute_value_norm R in
  let Z i:=@ContinuousMultilinear.space R i R^o R^o N N hN hN in
  let ev i:=@ContinuousMultilinear.evaluation R i R^o R^o N N hN hN in
  let ZN i:=@ContinuousMultilinear.norm R i R^o R^o N N hN hN in
  exists (D:forall i,R->Z i) (M:nat->R),forall i,
    (forall t,has_norm_higher_differential N ev ZN (fun _=>True) phi i t (D i t)) /\
    norm_class_zero N (ZN i) (fun _=>True) (D i) /\
    0<M i /\(forall t,ZN i (D i t)<=M i) /\
    forall t,t<0 \/1<t ->D i t= 0.
Proof.
move=>hPhi N hN Z ev ZN.
have hZ i:is_continuous_multilinear_space N N (ev i) (ZN i).
  exact:ContinuousMultilinear.laws.
pose K:set R^o:=[set t|0<=t<= 1].
have hIdentity:continuous (fun t:real_line_metric R=>(t:real_norm_metric_space hN)).
  apply:(@metric_fixed_lipschitz_continuous R [the metricType R of real_line_metric R] [the metricType R of real_norm_metric_space hN]
    (fun t=>t) 1 (@ler01 R))=>x y.
  change (is_true (`|x-y|<= 1*mdist (x:real_line_metric R) y)).
  by rewrite real_line_metric_distanceE mul1r.
have hImage:(fun t:real_line_metric R=>(t:real_norm_metric_space hN)) @` `[0,1]= K.
  apply/seteqP; split=>t.
  - move=>[s hs <-]; move:hs; by rewrite /= in_itv /= .
  - move=>ht; exists t; last reflexivity; by rewrite /= in_itv /= .
have hCompact:compact [set t:real_norm_metric_space hN|K t].
  rewrite -hImage; exact:(continuous_compact (continuous_subspaceT hIdentity) (@segment_compact R 0 1)).
have hOff t:~K t ->phi t= 0.
  move=>ht; apply:(positive_interval_bump_zero hPhi).
  case:(pselect (t<= 0))=>h0; first by left.
  right; apply:contrapT=>hNot.
  have ht0:0<t by rewrite ltNge; exact/negP.
  have ht1:t<1 by rewrite ltNge; exact/negP.
  apply:ht; apply/andP; split; exact:ltW.
have hEach i:exists p:(R->Z i)*R,
    (forall t,has_norm_higher_differential N ev ZN (fun _=>True) phi i t (p.1 t)) /\
    norm_class_zero N (ZN i) (fun _=>True) p.1 /\
    0<p.2 /\(forall t,ZN i (p.1 t)<=p.2) /\forall t,t<0 \/1<t ->p.1 t= 0.
  have hSmooth:=positive_interval_bump_smooth hPhi i.
  have [E [M [hE [hM [hBound hZero]]]]]:=@norm_compact_support_higher_differential_bound R
    R^o R^o N N hN hN Z ev ZN hZ K phi i hCompact hOff hSmooth.
  have [_ [D [hD hCont]]]:=hSmooth.
  have hEqual t:D t= E t:=norm_higher_differential_unique hN hN hZ (hD t Logic.I) (hE t).
  exists (D,M); split; first by move=>t; exact:(hD t Logic.I).
  split; first exact hCont.
  split; first exact hM.
  split; first by move=>t; change (is_true (ZN i (D t)<=M)); rewrite hEqual; exact:hBound.
  move=>t ht; change (D t= 0); rewrite hEqual; apply:hZero=>/andP [h0 h1]; case:ht=>h.
  - by have:=lt_le_trans h h0; rewrite ltxx.
  - by have:=le_lt_trans h1 h; rewrite ltxx.
pose p i:=projT1 (cid (hEach i)).
have hp i:=projT2 (cid (hEach i)).
exists (fun i=>(p i).1),(fun i=>(p i).2); exact hp.
Qed.
