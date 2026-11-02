(** Federer (1969), 2.5.17, p. 111: "Two such functions g1 and g2 induce the
    same Daniell integral if and only if there exists a real number c such
    that g1(x) - g2(x) = c for all but countably many x in R." The
    Riemann-Stieltjes integral is linear in the integrator, so the statement
    concerns the integrator h = g1 - g2 - c. If h vanishes off a countable
    set C, then every segment whose end points lie outside C admits
    sequences of arbitrarily small mesh avoiding C, the sums over them
    vanish, and so does the integral. The existence of points outside C in
    every open interval is derived from the Lebesgue measure L^1 of 2.5.17:
    countable sets have L^1 measure zero, open intervals do not. Conversely,
    if the Daniell integral induced by h vanishes, so do its positive and
    negative variations and the measures psi^+ and psi^- on open intervals;
    the identity h(b) - h(a) = psi^+{a < x < b} - psi^-{a < x < b} at points
    of continuity makes h constant on the points of continuity, whose
    complement is countable by 2.5.16. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealMetricBackground RealMetricCompleteness ExtendedRealBoundsUP
  ExtendedRealBounds NonnegativeSum CurveVariationUP CurveArcLength CurveDiscontinuities
  FunctionLatticeUP FunctionLatticeRegularityUP PositiveLatticeRegularity DaniellIntegralUP
  MonotoneDaniellIntegralUP DaniellVariationUP DaniellVariationBounds DaniellVariationFunctionals
  DaniellRepresentation DaniellCoverUP RegularDaniellEnvelope RealIntegralFunctionalUP MeasureUP
  MeasureBasic CompactSupportFunctionUP CompactSupportFunctionLattice StieltjesSums
  StieltjesIntegral StieltjesDaniellIntegral IntervalBumpFunctions StieltjesInducedMeasures
  StieltjesMonotone LebesgueLineMeasure StieltjesContinuityPoints.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CountableAvoidance.
Variable R : realType.

(** Source for [open_interval_avoid_countable]: every nonempty open
    interval contains a point outside a given countable set, because
    countable sets have L^1 measure zero and L^1{x : a < x < b} = b - a,
    Federer 2.5.17, p. 111. *)
Lemma open_interval_avoid_countable (C : set R) (a b : R) :
  countable C -> a < b -> exists z, a < z < b /\ ~ C z.
Proof.
move=> hC hab.
have [L1 [hm [_ [_ [hopen hclosed]]]]] := @lebesgue_line_measure_exists R.
apply: contrapT=> hnot.
have hsub : `]a, b[ `<=` \bigcup_(B in [set [set x] | x in C]) B.
  move=> x hx; have hCx : C x.
    apply: contrapT=> hCx; apply: hnot; exists x; split=> //.
  by exists [set x]; [exists x | ].
have hF : countable [set [set x] | x in C] := sub_countable (card_image_le _ C) hC.
have h0 : nonnegative_sum [set [set x] | x in C] L1 = 0%E.
  apply: nonnegative_sum_zero=> B [x _ <-].
  have -> : [set x] = `[x, x].
    apply/seteqP; split=> y; rewrite /= in_itv /=; first by move=> ->; rewrite lexx.
    by move=> /andP[h1 h2]; apply/le_anti; rewrite h2 h1.
  by rewrite hclosed // subrr.
have hle := measure_countable_cover hm hF hsub.
rewrite h0 hopen ?(ltW hab) // lee_fin in hle.
by move: hle; rewrite subr_le0 leNgt hab.
Qed.

(** Source for [avoiding_partition_steps]: a segment [a, b] with end
    points outside a countable set C and b - a <= n d/4 admits a sequence
    a = t_1 <= u_1 <= ... <= t_(m+1) = b of mesh below d whose terms avoid
    C, Federer 2.5.17, p. 111. *)
Lemma avoiding_partition_steps (C : set R) (d : R) (n : nat) :
  countable C -> 0 < d -> forall a b, a <= b -> b - a <= n%:R * (d / 4) -> ~ C a -> ~ C b ->
  exists w, is_tagged_partition a b w /\ tagged_mesh_lt d w /\ (forall x, x \in w -> ~ C x).
Proof.
move=> hC hd.
have hsmall : forall a b, a <= b -> b - a < d -> ~ C a -> ~ C b ->
    exists w, is_tagged_partition a b w /\ tagged_mesh_lt d w /\ (forall x, x \in w -> ~ C x).
  move=> a b hab hba hCa hCb; exists [:: a; a; b]; split; last split.
  - split; first by rewrite /= lexx hab.
    by split=> //; split.
  - by rewrite /= hba.
  - by move=> x; rewrite !inE => /orP[/eqP->|/orP[/eqP->|/eqP->]].
elim: n=> [|n ih] a b hab hn hCa hCb.
  by apply: hsmall=> //; move: hn; rewrite mul0r => hn; lra.
case: (ltP (b - a) d)=> [hba|hba]; first exact: hsmall.
have hlt : a + d / 4 < a + d / 2 by lra.
have [z [/andP[hz1 hz2] hCz]] := open_interval_avoid_countable hC hlt.
have hzb : z <= b by lra.
have hn' : b - z <= n%:R * (d / 4).
  by move: hn; rewrite -addn1 natrD mulrDl mul1r => hn; lra.
have [w' [hw' [hm' hC']]] := ih z b hzb hn' hCz hCb.
case: w' hw' hm' hC'=> [|t rest] [hs [hodd [hh hl]]] hm' hC'; first by [].
rewrite /= in hh; subst t.
exists [:: a, a, z & rest]; split; last split.
- split; first by rewrite /= lexx /= (ltW (lt_trans _ hz1)) ?hs //; lra.
  split; first by rewrite /= negbK.
  by split.
- by rewrite tagged_mesh_lt_cons hm' andbT; lra.
- move=> x; rewrite 2!inE => /orP[/eqP->|/orP[/eqP->|hx]] //.
  exact: hC' hx.
Qed.

(** Source for [avoiding_partition]: every segment with end points
    outside a countable set C admits sequences of arbitrarily small mesh
    avoiding C, Federer 2.5.17, p. 111. *)
Lemma avoiding_partition (C : set R) (a b d : R) :
  countable C -> 0 < d -> a <= b -> ~ C a -> ~ C b ->
  exists w, is_tagged_partition a b w /\ tagged_mesh_lt d w /\ (forall x, x \in w -> ~ C x).
Proof.
move=> hC hd hab hCa hCb.
have hd4 : 0 < d / 4 by lra.
have h0 : 0 <= (b - a) / (d / 4) by rewrite divr_ge0 // ?subr_ge0 // ltW.
have hn := archi_boundP h0; rewrite ltr_pdivrMr // in hn.
exact: (avoiding_partition_steps hC hd (a := a) (b := b) hab (ltW hn) hCa hCb).
Qed.

(** Source for [stieltjes_sum_vanishing_integrator]: the sum vanishes
    when the integrator vanishes at every term of the sequence, Federer
    2.5.17, p. 110. *)
Lemma stieltjes_sum_vanishing_integrator (f k : R -> R) (w : seq R) :
  (forall x, x \in w -> k x = 0) -> stieltjes_sum f k w = 0.
Proof.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|u [|t' rest]]] hsize hk //.
have ht : t \in t :: u :: t' :: rest by rewrite inE eqxx.
have ht' : t' \in t :: u :: t' :: rest by rewrite !inE eqxx !orbT.
rewrite stieltjes_sum_cons (hk t ht) (hk t' ht') subrr mulr0 add0r.
apply: ih; first by move: hsize; rewrite /= ltnS; exact: ltnW.
by move=> x hx; apply: hk; rewrite 2!inE hx !orbT.
Qed.

End CountableAvoidance.

Section Difference.
Variable R : realType.
Local Notation KR := (@compactly_supported_continuous_functions R R).
Variables g1 g2 : R -> R.
Variable c : R.
Local Notation k := (fun x : R => g1 x - g2 x - c).

(** Source for [stieltjes_sum_difference]: the sums are linear in the
    integrator and vanish for constant integrators, Federer 2.5.17,
    p. 110. *)
Lemma stieltjes_sum_difference (f : R -> R) (w : seq R) :
  stieltjes_sum f k w = stieltjes_sum f g1 w - stieltjes_sum f g2 w.
Proof.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|u [|t' rest]]] hsize; try by rewrite /= subrr.
rewrite !stieltjes_sum_cons ih /=; last by move: hsize; rewrite /= ltnS; exact: ltnW.
ring.
Qed.

(** Source for [difference_chain_sum_le]: the chain sums of 2.5.16 of
    g1 - g2 - c are at most the sums of those of g1 and g2, Federer
    2.5.16, p. 109. *)
Lemma difference_chain_sum_le (s : seq R) :
  chain_sum (k : R -> real_line_metric R) s
    <= chain_sum (g1 : R -> real_line_metric R) s + chain_sum (g2 : R -> real_line_metric R) s.
Proof.
elim: s=> [|t [|u rest] ih]; try by rewrite /= addr0.
rewrite !chain_sum_cons !real_line_metric_distanceE /=.
have hd : `|g1 t - g2 t - c - (g1 u - g2 u - c)| <= `|g1 t - g1 u| + `|g2 t - g2 u|.
  have -> : g1 t - g2 t - c - (g1 u - g2 u - c) = (g1 t - g1 u) - (g2 t - g2 u) by ring.
  exact: ler_normB.
by rewrite [X in _ <= X]addrACA; exact: lerD hd ih.
Qed.

(** Source for [difference_variation_le]: V_a^b (g1 - g2 - c) <=
    V_a^b g1 + V_a^b g2, Federer 2.5.16, p. 109. *)
Lemma difference_variation_le (a b : R) :
  (curve_variation (k : R -> real_line_metric R) a b
    <= curve_variation (g1 : R -> real_line_metric R) a b
       + curve_variation (g2 : R -> real_line_metric R) a b)%E.
Proof.
apply: extended_real_sup_least=> v [s [hs ->]].
apply: (@le_trans _ _ ((chain_sum (g1 : R -> real_line_metric R) s)%:E
  + (chain_sum (g2 : R -> real_line_metric R) s)%:E)%E).
  by rewrite -EFinD lee_fin; exact: difference_chain_sum_le.
by apply: leeD; apply: extended_real_sup_upper; exists s.
Qed.

Hypothesis hg1 : curve_locally_finite_variation (g1 : R -> real_line_metric R).
Hypothesis hg2 : curve_locally_finite_variation (g2 : R -> real_line_metric R).

(** Source for [difference_locally_finite_variation]: g1 - g2 - c has
    finite variation on every segment, Federer 2.5.16, p. 109. *)
Lemma difference_locally_finite_variation :
  curve_locally_finite_variation (k : R -> real_line_metric R).
Proof.
move=> a b hab; apply: le_lt_trans (difference_variation_le a b) _.
rewrite -(fineK (curve_variation_fin_num hg1 hab)) -(fineK (curve_variation_fin_num hg2 hab)).
by rewrite -EFinD ltry.
Qed.

(** Source for [stieltjes_integral_difference]: the Riemann-Stieltjes
    integral is linear in the integrator and vanishes for constant
    integrators, Federer 2.5.17, p. 111. *)
Lemma stieltjes_integral_difference (f : R -> R) (a b : R) :
  continuous f -> a <= b ->
  stieltjes_integral k f a b = stieltjes_integral g1 f a b - stieltjes_integral g2 f a b.
Proof.
move=> hf hab; apply/esym.
apply: (stieltjes_integral_unique difference_locally_finite_variation hf hab)=> e he.
have he2 : 0 < e / 2 by lra.
have [d1 [hd1 h1]] := stieltjes_integral_limit hg1 hf hab he2.
have [d2 [hd2 h2]] := stieltjes_integral_limit hg2 hf hab he2.
exists (Order.min d1 d2); split; first by rewrite lt_min hd1 hd2.
move=> w hw hm.
have hmin1 : Order.min d1 d2 <= d1 by rewrite ge_min lexx.
have hmin2 : Order.min d1 d2 <= d2 by rewrite ge_min lexx orbT.
have e1 := h1 w hw (tagged_mesh_lt_le hmin1 hm).
have e2 := h2 w hw (tagged_mesh_lt_le hmin2 hm).
rewrite stieltjes_sum_difference.
have -> : stieltjes_sum f g1 w - stieltjes_sum f g2 w
    - (stieltjes_integral g1 f a b - stieltjes_integral g2 f a b)
  = (stieltjes_sum f g1 w - stieltjes_integral g1 f a b)
    - (stieltjes_sum f g2 w - stieltjes_integral g2 f a b) by ring.
apply: le_lt_trans (ler_normB _ _) _.
by rewrite (splitr e); exact: (ltrD e1 e2).
Qed.

(** Source for [induced_daniell_difference]: the induced Daniell
    integral is linear in the integrator and vanishes for constant
    integrators, Federer 2.5.17, p. 111. *)
Lemma induced_daniell_difference (f : R -> R) :
  KR f -> induced_daniell k f = induced_daniell g1 f - induced_daniell g2 f.
Proof.
move=> hf; have [M [hM0 hM]] := compact_support_bound hf.
have hab : - (M + 1) <= M + 1 by lra.
have hz : forall x, f x <> 0 -> - (M + 1) < x < M + 1.
  by move=> x hx; have := hM x hx; rewrite ler_norml => /andP[h1 h2]; apply/andP; split; lra.
rewrite (induced_daniell_value difference_locally_finite_variation hf hab hz).
rewrite (induced_daniell_value hg1 hf hab hz) (induced_daniell_value hg2 hf hab hz).
exact: stieltjes_integral_difference (KR_continuous hf) hab.
Qed.

End Difference.

Section Uniqueness.
Variable R : realType.
Local Notation KR := (@compactly_supported_continuous_functions R R).
Local Notation KRp := (positive_function_lattice KR).

(** Source for [induced_daniell_countable_zero]: an integrator vanishing
    off a countable set induces the zero Daniell integral, Federer 2.5.17,
    p. 111. *)
Lemma induced_daniell_countable_zero (h : R -> R) (C : set R) :
  curve_locally_finite_variation (h : R -> real_line_metric R) -> countable C ->
  (forall x, ~ C x -> h x = 0) -> forall f, KR f -> induced_daniell h f = 0.
Proof.
move=> hh hC hz f hf.
have [M [hM0 hM]] := compact_support_bound hf.
have hlt1 : - M - 1 < - M by lra.
have [a [/andP[ha1 ha2] hCa]] := open_interval_avoid_countable hC hlt1.
have hlt2 : M < M + 1 by lra.
have [b [/andP[hb1 hb2] hCb]] := open_interval_avoid_countable hC hlt2.
have hab : a <= b by lra.
have hzab : forall x, f x <> 0 -> a < x < b.
  by move=> x hx; have := hM x hx; rewrite ler_norml => /andP[h1 h2]; apply/andP; split; lra.
rewrite (induced_daniell_value hh hf hab hzab).
apply/eqP; rewrite -normr_eq0 eq_le normr_ge0 andbT.
apply/ler_addgt0Pr=> e he; rewrite add0r.
have [d [hd hlim]] := stieltjes_integral_limit hh (KR_continuous hf) hab he.
have [w [hw [hm hwC]]] := avoiding_partition hC hd hab hCa hCb.
have := hlim w hw hm.
rewrite (stieltjes_sum_vanishing_integrator f (fun x hx => hz x (hwC x hx))) sub0r normrN.
exact: ltW.
Qed.

(** Source for [induced_daniell_zero_constant]: an integrator inducing
    the zero Daniell integral is constant off a countable set, Federer
    2.5.17, p. 111. *)
Lemma induced_daniell_zero_constant (h : R -> R) :
  curve_locally_finite_variation (h : R -> real_line_metric R) ->
  (forall f, KR f -> induced_daniell h f = 0) -> exists c : R, countable [set x | h x <> c].
Proof.
move=> hh hz.
have hL := @compactly_supported_continuous_functions_lattice R R.
have hD := induced_daniell_is_daniell hh.
have hne : exists f, KR f by exists (fun _ => 0); exact: compactly_supported_zero_function.
have [P [Q [psip [psim [hP [hQ [hm [hn [hr [hs [hi [hj _]]]]]]]]]]]] :=
  daniell_integral_representation hL hD hne.
have hLp : is_function_lattice KRp := positive_lattice_is_lattice hL.
have henvP := regular_representing_measure_envelope hLp hm hi hr.
have henvQ := regular_representing_measure_envelope hLp hn hj hs.
have hAP := positive_variation_monotone_daniell hL hD hP.
have hAQ := negative_variation_monotone_daniell hL hD hQ.
have hbound := induced_cost_bound hh hP hQ henvP henvQ.
have hbump : forall a b n, KRp (interval_bump a b n).
  by move=> a b n; split; [exact: interval_bump_member | move=> x; exact: interval_bump_ge0].
have hP0 : forall a b, psip `]a, b[ = 0%E.
  move=> a b; apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  have hsup := bump_cost_open_interval a b hAP henvP.
  apply: (extended_real_supremum_least hsup)=> z [n ->]; rewrite lee_fin.
  apply: (daniell_positive_variation_least hP (hbump a b n))=> k [hk _].
  by rewrite (hz k hk).
have hQ0 : forall a b, psim `]a, b[ = 0%E.
  move=> a b; apply/eqP; rewrite eq_le (measure_nonnegative hn) andbT.
  have hsup := bump_cost_open_interval a b hAQ henvQ.
  apply: (extended_real_supremum_least hsup)=> z [n ->]; rewrite lee_fin.
  apply: (daniell_positive_variation_least hQ (hbump a b n))=> k [hk _].
  by rewrite (hz k hk) oppr0.
have hconst : forall x y, x < y -> h @ x --> h x -> h @ y --> h y -> h y = h x.
  move=> x y hxy hcx hcy.
  have := induced_increment_open hh hP hQ henvP henvQ hm hn hbound hxy hcx hcy.
  rewrite hP0 hQ0 sube0 => /(f_equal fine) /= /eqP; rewrite subr_eq0 => /eqP.
  by [].
have hjump : forall x, ~ (h @ x --> h x) -> curve_jump_points (h : R -> real_line_metric R) x.
  by move=> x hx; exact/(curve_jump_points_iff hh (@real_line_metric_complete R) x).
have hcount := curve_jump_points_countable hh.
case: (pselect (exists x0, h @ x0 --> h x0))=> [[x0 hx0]|hnone].
- exists (h x0); apply: (sub_countable _ hcount); apply: subset_card_le=> x hx.
  apply: hjump=> hcx; apply: hx.
  case: (ltgtP x x0)=> [hlt|hgt|->] //.
  + by apply/esym; exact: hconst hlt hcx hx0.
  + exact: hconst hgt hx0 hcx.
- exists 0; apply: (sub_countable _ hcount); apply: subset_card_le=> x _.
  by apply: hjump=> hcx; apply: hnone; exists x.
Qed.

(** Source for [stieltjes_induced_daniell_unique]: two integrators g1
    and g2 of finite variation on segments induce the same Daniell
    integral if and only if g1(x) - g2(x) = c for all but countably many
    x, for some real c, Federer 2.5.17, p. 111. *)
Theorem stieltjes_induced_daniell_unique (g1 g2 : R -> R) :
  curve_locally_finite_variation (g1 : R -> real_line_metric R) ->
  curve_locally_finite_variation (g2 : R -> real_line_metric R) ->
  (forall f, KR f -> induced_daniell g1 f = induced_daniell g2 f) <->
  exists c : R, countable [set x | g1 x - g2 x <> c].
Proof.
move=> hg1 hg2; split.
- move=> heq.
  have hk := difference_locally_finite_variation 0 hg1 hg2.
  have [c hc] := induced_daniell_zero_constant hk
    (fun f hf => etrans (induced_daniell_difference 0 hg1 hg2 hf) (etrans (congr1 (fun t => t - induced_daniell g2 f) (heq f hf)) (subrr _))).
  exists c; move: hc.
  suff -> : [set x | g1 x - g2 x - 0 <> c] = [set x | g1 x - g2 x <> c] by [].
  by apply/seteqP; split=> x /=; rewrite subr0.
- move=> [c hc] f hf.
  have hk := difference_locally_finite_variation c hg1 hg2.
  have hz : forall x, ~ [set x | g1 x - g2 x <> c] x -> g1 x - g2 x - c = 0.
    move=> x hx; apply/eqP; rewrite subr_eq0; apply/eqP.
    by apply: contrapT=> hne; exact: hx hne.
  have := induced_daniell_countable_zero hk hc hz hf.
  rewrite (induced_daniell_difference c hg1 hg2 hf) => /eqP.
  by rewrite subr_eq0 => /eqP.
Qed.

End Uniqueness.
