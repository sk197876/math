(** Federer (1969), 3.3.19, p. 306: mass
    control for original ball tests whose hit children
    have the proved strict tangential separation. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP Bilinear InnerNorm InnerNormInequalities InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws CircularDiscTreeUP CircularDiscTreeTopology CircularDiscLimitUP
  CircularDiscPieceTranslations CircularDiscPieceHausdorffMass CircularDiscSubfamilyMass HausdorffTranslatedBallPair
  FiniteTwoDistinctMembers FiniteTangentialBallPacking HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic MeasureSplit MeasureFiniteAdditivity TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Mass.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation N:=(inner_norm (@euclidean_inner_productP R 2)).
Local Notation B:=(@euclidean_inner_product R 2).
Local Notation hE:=(@euclidean_inner_productP R 2).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_tangential_ball_mass]: actual
    original level pieces covering A intersect B(a,t),
    with all hit centres within t+rho_j of a and
    tangent spacing >6rho_j, have total ball mass <=t.
    Four or more pieces use strict packing; two use
    actual vertex separation; three use either full masses
    or a proved disjoint translated extreme-pair test.
    This supports the last claim in 3.3.19, p. 306;
    its geometric premises are discharged separately for
    all sufficiently late small original balls. *)
Theorem circular_disc_tangential_ball_mass j (F:{fset E}) (a e:E) (t:R):
  (F `<=` H j)%fset ->(2<=#|` F|)%N ->0<=t ->N e= 1 ->
  (exists c:E,c \in F /\metric_closed_ball c (rho j) a) ->
  (forall c,c \in F ->mdist c a<=t+rho j) ->
  (forall c d,c \in F ->d \in F ->c!=d ->6* rho j<`|B (c-d) e|) ->
  (A `&` metric_closed_ball a t) `<=`
    (A `&` (\bigcup_(c in [set` F]) metric_closed_ball c (rho j))) ->
  (mu (A `&` metric_closed_ball a t)<=t%:E)%E.
Proof.
move=>hFH hCount ht he [c0 [hc0 ha0]] hNear hSpacing hCover.
pose h:= rho j.
have hh:0<h:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho
  (@FactorialDiscScales.laws R) j.
pose f:= fun x:E=>B x e.
have hCoordinate x y:`|f x-f y|<=mdist x y.
  have hCauchy:= inner_cauchy hE (x-y) e.
  by rewrite he mulr1 (bilBl (inner_bilinear hE)) -inner_metric_distanceE in hCauchy.
have hStrict x y:x \in F ->y \in F ->x!=y ->6* h<`|f x-f y|.
  move=>hx hy hDifferent;rewrite /f -(bilBl (inner_bilinear hE)).
  exact:hSpacing x y hx hy hDifferent.
have hPacking:= @finite_tangential_ball_count R E f hCoordinate F a t h hCount hh ht hNear hStrict.
have [x0 [y0 [hx0 [hy0 hDifferent]]]]:= @finite_two_distinct_members E F hCount.
have hOther:exists w:E,w \in F /\c0!=w.
  case:(eqVneq c0 x0)=>[hEq|hNe].
  - exists y0;split=>//;by rewrite hEq.
  - by exists x0;split.
have [w [hw hCW]]:= hOther.
have hFar:6* h<mdist c0 w:= lt_le_trans (hStrict c0 w hc0 hw hCW) (hCoordinate c0 w).
have hTriangle:= metric_triangle c0 a w.
have hCentreVertex:mdist c0 a<=h:= ha0.
have hW:mdist a w<=t+h by rewrite metric_sym;exact:hNear w hw.
have hT4:4* h<t by nra.
have hMu:= @hausdorff_measure_is_measure R E 1.
pose T:= A `&` metric_closed_ball a t.
have hFull:(mu T<=(2* h*#|` F|%:R)%:E)%E.
  rewrite -(@circular_disc_level_subfamily_mass R H hH A hA j F hFH).
  exact:(@measure_mono R E mu hMu _ _ hCover).
case:(leqP 4 #|` F|)=>[hMany|hFew].
- have hN4:(4<=#|` F|%:R:>R) by rewrite ler_nat.
  have hBound:2* h*#|` F|%:R<=t by nra.
  exact:(le_trans hFull (lee_tofin hBound)).
case:(leqP #|` F| 2)=>[hTwo|hThree].
- have hN2:(#|` F|%:R<=2:>R) by rewrite ler_nat.
  have hBound:2* h*#|` F|%:R<=t by nra.
  exact:(le_trans hFull (lee_tofin hBound)).
have hCard3:#|` F|= 3%N by apply/eqP;rewrite eqn_leq;apply/andP;by split.
case:(leP (6* h) t)=>[hLarge|hSmall].
- rewrite hCard3 in hFull.
  have hBound:2* h*(3:R)<=t by nra.
  exact:(le_trans hFull (lee_tofin hBound)).
have hAtLeast3:(3<=#|` F|)%N by rewrite hCard3.
have [c [d [hc [hd hCD]]]]:= @finite_tangential_ball_extreme_pair R E f hCoordinate F h hAtLeast3 hh hStrict.
have hCDDifferent:c!=d.
  apply/eqP=>hEqual;rewrite hEqual mdistxx in hCD;nra.
pose K:=(F `\ c)%fset.
pose Q:=(K `\ d)%fset.
have hcK:c \in F:= hc.
have hdK:d \in K by rewrite /K in_fsetD1 eq_sym hCDDifferent hd.
have hCard1:#|` F|=(#|` K|).+1 by rewrite (cardfsD1 c) hc add1n.
have hCard2:#|` K|=(#|` Q|).+1 by rewrite (cardfsD1 d) hdK add1n.
have hRestCard:#|` Q|= 1%N.
  apply:succn_inj;apply:succn_inj;by rewrite -hCard2 -hCard1 hCard3.
have hQSubset:(Q `<=` H j)%fset.
  apply/fsubsetP=>z hz.
  have /andP[_ hzK]:(z!=d) && (z \in K) by move:hz;rewrite /Q in_fsetD1.
  have /andP[_ hzF]:(z!=c) && (z \in F) by move:hzK;rewrite /K in_fsetD1.
  exact:fsubsetP hFH z hzF.
pose Pc:= A `&` metric_closed_ball c h.
pose Pd:= A `&` metric_closed_ball d h.
pose U:= A `&` (\bigcup_(z in [set` Q]) metric_closed_ball z h).
have hU:mu U=(2* h)%:E.
  rewrite (@circular_disc_level_subfamily_mass R H hH A hA j Q hQSubset) hRestCard mulr1;by [].
have [_ hCompact]:= @circular_disc_limit_nonempty_compact R H hH A hA.
have hClosed:closed Pc.
  apply:closedI;last exact:metric_closed_ball_closed.
  exact:compact_closed (@metric_hausdorff R [the metricType R of E]) hCompact.
have hTranslation:= @circular_disc_level_pieces_translates R H hH A hA j c d
  (fsubsetP hFH c hc) (fsubsetP hFH d hd).
have hPairFar:2* t<N (d-c).
  rewrite -inner_metric_distanceE metric_sym.
  have hFirst:2* t<12* h by nra.
  exact:lt_trans hFirst hCD.
have hPair:= @hausdorff_translated_ball_pair_bound R (R_n R 2) B hE Pc a (d-c) t hClosed hPairFar.
rewrite hTranslation in hPair.
have hPc:mu Pc=(2*h)%:E:=@circular_disc_piece_Hausdorff_mass R H hH A hA j c (fsubsetP hFH c hc).
rewrite hPc in hPair.
have hCoverThree:T `<=` (Pc `&` metric_closed_ball a t) `|`
    ((Pd `&` metric_closed_ball a t) `|` U).
  move=>x hxT.
  have [hxA [z hz hxZ]]:= hCover x hxT.
  case:(eqVneq z c)=>[hEqual|hzC].
  - rewrite hEqual in hxZ;left;split;first by split.
    exact:hxT.2.
  - case:(eqVneq z d)=>[hEqual|hzD].
    + rewrite hEqual in hxZ;right;left;split;first by split.
      exact:hxT.2.
    + right;right;split=>//.
      have hzQ:z \in Q by rewrite /Q in_fsetD1 hzD /K in_fsetD1 hzC hz.
      by exists z.
have hUpper:= @measure_binary_cover R E mu hMu T _ _ hCoverThree.
have hRest:= @measure_binary_cover R E mu hMu
  ((Pd `&` metric_closed_ball a t) `|` U) _ _ (fun x hx=>hx).
have hCombined:= le_trans hUpper (leeD2l (mu (Pc `&` metric_closed_ball a t)) hRest).
rewrite addeA in hCombined.
have hAll:= le_trans hCombined (leeD2r (mu U) hPair).
rewrite hU -EFinD in hAll.
have hBound:2* h+2* h<=t by lra.
exact:(le_trans hAll (lee_tofin hBound)).
Qed.
End Mass.
