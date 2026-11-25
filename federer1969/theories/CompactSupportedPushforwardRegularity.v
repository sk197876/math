(** Federer (1969), 3.2.6, pp. 245–246: a bounded
    curve source permits a finite compact-support reduction.
    This supporting image-measure regularity argument uses
    2.2.2–2.2.3 and the compact-image part of 2.2.17. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasurePushforward PushforwardMeasurableSets
  BorelRegularMeasureUP BorelOpenApproximation TopologicalBorel ExtendedRealOrderTopology ExtendedRealReciprocalBounds
  MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_supported_continuous_pushforward_borel_regular]:
    supporting finite image measure in Federer 3.2.6,
    p. 245. Compact support makes complements of source
    open neighborhoods have closed images, providing target
    open outer approximants. No injectivity is assumed. *)
Theorem compact_supported_continuous_pushforward_borel_regular (R:realType) (X:metricType R)
    (Y:topologicalType) (mu:set X->\bar R) (hm:is_measure mu)
    (hr:is_borel_regular_measure mu) (K:set X) (f:X->Y):
  hausdorff_space Y -> compact K -> continuous f -> mu setT< +oo -> mu (~` K)=0 ->
  is_borel_regular_measure (measure_pushforward f mu).
Proof.
move=>hY hK hf hFin hOff.
pose nu:=measure_pushforward f mu.
have hn:=@measure_pushforward_is_measure R X Y f mu hm.
have hOpen U:open U -> measure_measurable nu U.
  move=>hU; apply:pushforward_measurable_from_preimage.
  exact (borel_regular_open_measurable hr ((continuousP f).1 hf U hU)).
have hApprox S (e:R):(0<e)%R -> exists W,open W /\ S `<=` W /\ nu W<nu S+e%:E.
  move=>he.
  have [B [hSB [hB hVal]]]:=borel_regular_cover hr (f @^-1` S).
  have hCover:B `<=` \bigcup_(j:nat) (@setT X) by move=>x _; exists 0%N.
  have [U [hU [hBU hSmall]]]:=@metric_borel_open_approximation R X mu hm B
    (fun _ :nat=>setT) e (fun V hV=>borel_regular_open_measurable hr hV) hB
    (fun _=>conj openT hFin) hCover he.
  have hCompact:compact (K `\` U).
    apply:(subclosed_compact _ hK).
    - exact:closedI (compact_closed (@metric_hausdorff R X) hK) (open_closedC hU).
    - by move=>x [hx _].
  have hImage:closed (f @` (K `\` U)).
    have hComp:compact (f @` (K `\` U)):=continuous_compact (continuous_subspaceT hf) hCompact.
    exact (compact_closed hY hComp).
  pose W:=~` (f @` (K `\` U)).
  have hW:open W:=closed_openC hImage.
  have hSW:S `<=` W.
    move=>y hy [x [hx hnU] hxy]; apply:hnU; apply:hBU; apply:hSB.
    change (S (f x)); by rewrite hxy.
  have hPre:f @^-1` W `<=` U `|` (~` K).
    move=>x hx; case:(pselect (U x))=>hUx; first by left.
    right=>hKx; apply:hx; exists x=>//; by split.
  have hBound:nu W<=mu U.
    have hb:=measure_binary_cover hm hPre; by rewrite hOff adde0 in hb.
  have hUB:mu U<=mu B+mu (U `\` B).
    have hb:=measure_split_upper hm U B.
    apply:le_trans hb _; apply:leeD; last exact:lexx.
    exact (@measure_mono R X mu hm (U `&` B) B (fun x hx=>hx.2)).
  have hBFin:mu B \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative hm B)); exact:le_lt_trans (measure_mono hm (subsetT B)) hFin.
  have hStrict:mu B+mu (U `\` B)<mu B+e%:E.
    by rewrite lteD2lE //.
  exists W; split=>//; split=>//.
  apply:le_lt_trans (le_trans hBound hUB) _.
  have hEq:mu B=nu S:=esym hVal.
  rewrite -hEq; exact hStrict.
constructor=>// S.
have hSFin:nu S \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hn S)).
  exact:le_lt_trans (measure_mono hm (subsetT (f @^-1` S))) hFin.
have hex j:exists W,open W /\ S `<=` W /\ nu W<nu S+((j.+1%:R:R)^-1)%:E.
  apply:hApprox; by rewrite invr_gt0 ltr0n.
have [W hW]:=choice hex.
pose B:=\bigcap_j W j.
exists B; split.
- move=>y hy j _; exact ((hW j).2.1 y hy).
- split.
  + apply:borel_set_countable_intersection; first exact:countableP.
    * by exists 0%N.
    * move=>j _; exact (open_borel_set (hW j).1).
  + apply/eqP; rewrite eq_le (measure_mono hn (fun y hy j _=>(hW j).2.1 y hy)) /=.
    change (is_true (nu B<=nu S)).
    rewrite -(fineK hSFin).
    apply:extended_real_reciprocal_upper_bound=>j.
    have hb:=le_lt_trans (measure_mono hn (fun y hy=>hy j Logic.I)) (hW j).2.2.
    rewrite -(fineK hSFin) -EFinD in hb; exact (ltW hb).
Qed.
