(** Federer (1969), 2.5.18(2), p. 112: "Therefore g_# maps the measures
    induced by h o g onto the measures induced by h." Here g is a continuous
    increasing map of R onto R; the hypothesis im g = R is added. The
    substitution formula of 2.5.18(2) gives mu_{h o g}(f o g) = mu_h(f) for
    f in K(R); composition with g is a bijection of K(R) onto itself, so the
    positive and negative variations of 2.5.5 satisfy the same relation. A
    regular measure representing a monotone Daniell integral is the envelope
    of 2.5.2; composition with g and with its inverse transports suiting
    sequences, so g_# maps the envelope for the variations of mu_{h o g}
    onto the envelope for those of mu_h, and envelopes are unique. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground ExtendedRealBoundsUP ExtendedRealBounds
  CurveVariationUP CurveArcLength FunctionLatticeUP FunctionLatticeRegularityUP
  PositiveLatticeRegularity DaniellIntegralUP DaniellVariationUP DaniellRepresentation
  DaniellCoverUP RegularDaniellEnvelope RealIntegralFunctionalUP MeasureUP MeasurePushforward
  CompactSupportFunctionUP CompactSupportFunctionLattice StieltjesSums StieltjesIntegral
  StieltjesDaniellIntegral IntervalBumpFunctions StieltjesInducedMeasures StieltjesSubstitution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section InducedPairs.
Variable R : realType.
Local Notation KR := (@compactly_supported_continuous_functions R R).
Local Notation KRp := (positive_function_lattice KR).

(** Source for [is_induced_measure_pair]: psi^+ and psi^- are measures
    induced by k in the sense of Federer 2.5.17, p. 111: K(R)+ regular
    measures representing the positive and negative variations of the
    Daniell integral induced by k. *)
Definition is_induced_measure_pair (k : R -> R) (psip psim : set R -> \bar R) : Prop :=
  exists P Q : (R -> R) -> R,
    is_daniell_positive_variation KR (induced_daniell k) P /\
    is_daniell_negative_variation KR (induced_daniell k) Q /\
    is_measure psip /\ is_measure psim /\
    is_function_lattice_regular KRp psip /\ is_function_lattice_regular KRp psim /\
    is_real_integral_functional psip KRp P /\ is_real_integral_functional psim KRp Q.

(** Source for [induced_measure_pair_exists]: every function of finite
    variation on segments induces measures, Federer 2.5.17, p. 111, by
    2.5.13, 2.5.6 and 2.5.3. *)
Lemma induced_measure_pair_exists (k : R -> R) :
  curve_locally_finite_variation (k : R -> real_line_metric R) ->
  exists psip psim, is_induced_measure_pair k psip psim.
Proof.
move=> hk.
have hL := @compactly_supported_continuous_functions_lattice R R.
have hD := induced_daniell_is_daniell hk.
have hne : exists f, KR f by exists (fun _ => 0); exact: compactly_supported_zero_function.
have [P [Q [psip [psim [hP [hQ [hm [hn [hr [hs [hi [hj _]]]]]]]]]]]] :=
  daniell_integral_representation hL hD hne.
by exists psip, psim, P, Q.
Qed.

(** Source for [daniell_cover_envelope_unique]: a set function is
    determined by the two clauses of the infimum of Federer 2.5.2,
    p. 92. *)
Lemma daniell_cover_envelope_unique (L : set (R -> R)) (A : (R -> R) -> R)
    (mu1 mu2 : set R -> \bar R) :
  is_daniell_cover_envelope L A mu1 -> is_daniell_cover_envelope L A mu2 -> mu1 = mu2.
Proof.
move=> h1 h2; apply/funext=> S; apply/le_anti/andP; split.
- by apply: (daniell_cover_greatest h2)=> f c hf hc; exact: (daniell_cover_lower h1 hf hc).
- by apply: (daniell_cover_greatest h1)=> f c hf hc; exact: (daniell_cover_lower h2 hf hc).
Qed.

(** Source for [KR_vanishing_outside]: a continuous function vanishing
    outside a segment belongs to K(R), Federer 2.5.13, p. 106. *)
Lemma KR_vanishing_outside (f : R -> R) (a b : R) :
  continuous f -> (forall x, f x <> 0 -> a <= x <= b) -> KR f.
Proof.
move=> hf hz; split; first exact: hf.
rewrite /real_function_support.
apply: (subclosed_compact (@closed_closure _ [set x | f x <> 0]) (@segment_compact R a b)).
rewrite [X in _ `<=` X]((closure_id _).1 (@segment_closed_real R a b)).
by apply: closureS=> x hx; rewrite /= in_itv /=; exact: hz.
Qed.

(** Source for [KR_comp_increasing]: composition with a continuous
    increasing map of R onto R preserves K(R), Federer 2.5.18(2),
    p. 112. *)
Lemma KR_comp_increasing (p f : R -> R) :
  continuous p -> (forall x y, x < y -> p x < p y) -> (forall z, exists x, p x = z) ->
  KR f -> KR (f \o p).
Proof.
move=> hpc hinc hsurj hf.
have [M [hM0 hM]] := compact_support_bound hf.
have [a ha] := hsurj (- M - 1).
have [b hb] := hsurj (M + 1).
apply: (KR_vanishing_outside (a := a) (b := b)).
  by move=> x; apply: continuous_comp; [exact: hpc | exact: (KR_continuous hf)].
move=> x /= hx; have := hM _ hx; rewrite ler_norml => /andP[h1 h2].
apply/andP; split.
- rewrite leNgt; apply/negP=> hxa; have := hinc _ _ hxa; rewrite ha; lra.
- rewrite leNgt; apply/negP=> hbx; have := hinc _ _ hbx; rewrite hb; lra.
Qed.

End InducedPairs.

Section ImageMeasures.
Variable R : realType.
Local Notation KR := (@compactly_supported_continuous_functions R R).
Local Notation KRp := (positive_function_lattice KR).
Variable g : R -> R.
Hypothesis hgc : continuous g.
Hypothesis hinc : forall x y, x < y -> g x < g y.
Hypothesis hsurj : forall z, exists x, g x = z.

(** Source for [increasing_inverse]: the inverse of the increasing map g
    of R onto R, Federer 2.5.18(2), p. 112. *)
Definition increasing_inverse (z : R) : R := sval (cid (hsurj z)).

(** Source for [increasing_inverseK]: g(g^{-1}(z)) = z, Federer
    2.5.18(2), p. 112. *)
Lemma increasing_inverseK (z : R) : g (increasing_inverse z) = z.
Proof. exact: svalP (cid (hsurj z)). Qed.

(** Source for [increasing_mono]: g is nondecreasing, Federer
    2.5.18(2), p. 112. *)
Lemma increasing_mono (x y : R) : x <= y -> g x <= g y.
Proof. by rewrite le_eqVlt => /orP[/eqP->|h]; [exact: lexx | exact: ltW (hinc h)]. Qed.

(** Source for [increasing_inverse_comp]: g^{-1}(g(x)) = x, Federer
    2.5.18(2), p. 112. *)
Lemma increasing_inverse_comp (x : R) : increasing_inverse (g x) = x.
Proof.
have h := increasing_inverseK (g x).
case: (ltgtP (increasing_inverse (g x)) x)=> [hlt|hgt|//].
- by have := hinc hlt; rewrite h ltxx.
- by have := hinc hgt; rewrite h ltxx.
Qed.

(** Source for [increasing_inverse_lt]: g^{-1} is increasing, Federer
    2.5.18(2), p. 112. *)
Lemma increasing_inverse_lt (z z' : R) : z < z' -> increasing_inverse z < increasing_inverse z'.
Proof.
move=> hzz'; rewrite ltNge; apply/negP=> hle.
have := increasing_mono hle; rewrite !increasing_inverseK => h.
by move: hzz'; rewrite ltNge h.
Qed.

(** Source for [increasing_inverse_continuous]: g^{-1} is continuous,
    Federer 2.5.18(2), p. 112. *)
Lemma increasing_inverse_continuous : continuous increasing_inverse.
Proof.
move=> z; apply/cvg_ballP=> e he.
set x := increasing_inverse z.
have h1 : g (x - e) < z by rewrite -[z]increasing_inverseK; apply: hinc; rewrite /x; lra.
have h2 : z < g (x + e) by rewrite -[z]increasing_inverseK; apply: hinc; rewrite /x; lra.
pose d := Order.min (z - g (x - e)) (g (x + e) - z).
have hd : 0 < d by rewrite /d lt_min !subr_gt0 h1 h2.
have hd1 : d <= z - g (x - e) by rewrite /d ge_min lexx.
have hd2 : d <= g (x + e) - z by rewrite /d ge_min lexx orbT.
suff : nbhs z [set t | ball x e (increasing_inverse t)] by [].
apply/nbhs_ballP; exists d=> // t; rewrite /ball /= ltr_norml => /andP[ht1 ht2].
have hl : g (x - e) < t by lra.
have hr : t < g (x + e) by lra.
have := increasing_inverse_lt hl; have := increasing_inverse_lt hr.
rewrite !increasing_inverse_comp ltr_norml => hr' hl'.
by apply/andP; split; lra.
Qed.

(** Source for [increasing_inverse_surjective]: g^{-1} maps R onto R,
    Federer 2.5.18(2), p. 112. *)
Lemma increasing_inverse_surjective (z : R) : exists x, increasing_inverse x = z.
Proof. by exists (g z); exact: increasing_inverse_comp. Qed.

(** Source for [KRp_comp]: composition with g preserves K(R)+, Federer
    2.5.18(2), p. 112. *)
Lemma KRp_comp (f : R -> R) : KRp f -> KRp (f \o g).
Proof. by move=> [hf h0]; split; [exact: KR_comp_increasing hgc hinc hsurj hf | move=> x; exact: h0]. Qed.

(** Source for [KRp_comp_inverse]: composition with g^{-1} preserves
    K(R)+, Federer 2.5.18(2), p. 112. *)
Lemma KRp_comp_inverse (f : R -> R) : KRp f -> KRp (f \o increasing_inverse).
Proof.
move=> [hf h0]; split; last by move=> x; exact: h0.
exact: KR_comp_increasing increasing_inverse_continuous increasing_inverse_lt
  increasing_inverse_surjective hf.
Qed.

(** Source for [comp_inverse_comp]: (f o g^{-1}) o g = f, Federer
    2.5.18(2), p. 112. *)
Lemma comp_inverse_comp (f : R -> R) : (f \o increasing_inverse) \o g = f.
Proof. by apply/funext=> x /=; rewrite increasing_inverse_comp. Qed.

(** Source for [positive_variation_comp]: if A1(f o g) = A2(f) for f in
    K(R), then the positive variations of 2.5.5 satisfy
    P1(f o g) = P2(f) for f in K(R)+, Federer 2.5.18(2), p. 112. *)
Lemma positive_variation_comp (A1 A2 P1 P2 : (R -> R) -> R) :
  (forall f, KR f -> A1 (f \o g) = A2 f) ->
  is_daniell_positive_variation KR A1 P1 -> is_daniell_positive_variation KR A2 P2 ->
  forall f, KRp f -> P1 (f \o g) = P2 f.
Proof.
move=> hA hP1 hP2 f hf.
have hs1 := hP1 _ (KRp_comp hf).
have hs2 := hP2 _ hf.
suff hset : daniell_interval_values KR A1 (f \o g) = daniell_interval_values KR A2 f.
  by rewrite hset in hs1; have := extended_real_supremum_unique hs1 hs2 => -[].
apply/seteqP; split=> v.
- move=> [k [[hk [hk0 hkf]] ->]].
  have hki : KRp (k \o increasing_inverse) := KRp_comp_inverse (conj hk hk0).
  exists (k \o increasing_inverse); split.
    split; first exact: hki.1.
    split; first exact: hki.2.
    by move=> x /=; have := hkf (increasing_inverse x); rewrite /= increasing_inverseK.
  by rewrite -(hA _ hki.1) comp_inverse_comp.
- move=> [k [[hk [hk0 hkf]] ->]].
  have hkg := KRp_comp (conj hk hk0).
  exists (k \o g); split; last by rewrite (hA _ hk).
  split; first exact: hkg.1.
  by split; [exact: hkg.2 | move=> x /=; exact: hkf].
Qed.

(** Source for [envelope_image]: g_# maps the envelope of 2.5.2 for P1
    onto the envelope for P2 when P1(f o g) = P2(f) for f in K(R)+,
    Federer 2.5.18(2), p. 112. *)
Lemma envelope_image (P1 P2 : (R -> R) -> R) (psi : set R -> \bar R) :
  (forall f, KRp f -> P1 (f \o g) = P2 f) ->
  is_daniell_cover_envelope KRp P1 psi ->
  is_daniell_cover_envelope KRp P2 (measure_pushforward g psi).
Proof.
move=> hP henv; constructor.
- move=> S f c [hf0 [hfmon hflim]] hc; rewrite /measure_pushforward.
  apply: (daniell_cover_lower henv (f := fun n => f n \o g)).
    split; first by move=> n; split; [exact (KRp_comp (hf0 n).1) | move=> x; exact ((hf0 n).2 (g x))].
    split; first by move=> n m hnm x; exact (hfmon n m hnm (g x)).
    by move=> x hx r hr; exact (hflim (g x) hx r hr).
  constructor.
  + move=> z [n ->]; rewrite (hP _ (hf0 n).1).
    exact: (extended_real_supremum_upper hc (ex_intro _ n erefl)).
  + move=> d hd; apply: (extended_real_supremum_least hc)=> z [n ->].
    rewrite -(hP _ (hf0 n).1); exact: hd (ex_intro _ n erefl).
- move=> S b hb; rewrite /measure_pushforward.
  apply: (daniell_cover_greatest henv)=> f c [hf0 [hfmon hflim]] hc.
  apply: (hb (fun n => f n \o increasing_inverse)).
    split; first by move=> n; split; [exact (KRp_comp_inverse (hf0 n).1) |
      move=> x; exact ((hf0 n).2 (increasing_inverse x))].
    split; first by move=> n m hnm x; exact (hfmon n m hnm (increasing_inverse x)).
    move=> x hx r hr; apply: hflim r hr; rewrite /= increasing_inverseK; exact: hx.
  have he : forall n, P2 (f n \o increasing_inverse) = P1 (f n).
    by move=> n; rewrite -(hP _ (KRp_comp_inverse (hf0 n).1)) comp_inverse_comp.
  constructor.
  + move=> z [n ->]; rewrite he.
    exact: (extended_real_supremum_upper hc (ex_intro _ n erefl)).
  + move=> d hd; apply: (extended_real_supremum_least hc)=> z [n ->].
    rewrite -he; exact: hd (ex_intro _ n erefl).
Qed.

Variable h : R -> R.
Hypothesis hh : curve_locally_finite_variation (h : R -> real_line_metric R).

(** Source for [comp_locally_finite_variation]: h o g has finite
    variation on every segment, Federer 2.5.18(2), p. 112. *)
Lemma comp_locally_finite_variation :
  curve_locally_finite_variation (h \o g : R -> real_line_metric R).
Proof.
move=> c d hcd; apply: le_lt_trans (curve_variation_comp_le h increasing_mono hcd) _.
exact: hh (increasing_mono hcd).
Qed.

(** Source for [induced_daniell_comp]: mu_{h o g}(f o g) = mu_h(f) for f
    in K(R), the substitution formula of Federer 2.5.18(2), p. 112. *)
Lemma induced_daniell_comp (f : R -> R) :
  KR f -> induced_daniell (h \o g) (f \o g) = induced_daniell h f.
Proof.
move=> hf.
have [M [hM0 hM]] := compact_support_bound hf.
set a := increasing_inverse (- (M + 1)); set b := increasing_inverse (M + 1).
have hab : a <= b by apply: ltW; apply: increasing_inverse_lt; lra.
have hz : forall x, f x <> 0 -> - (M + 1) < x < M + 1.
  by move=> x hx; have := hM x hx; rewrite ler_norml => /andP[h1 h2]; apply/andP; split; lra.
have hzg : forall x, (f \o g) x <> 0 -> a < x < b.
  move=> x /= hx; have /andP[h1 h2] := hz _ hx; apply/andP; split.
  - by rewrite -(increasing_inverse_comp x); exact: increasing_inverse_lt.
  - by rewrite -(increasing_inverse_comp x); exact: increasing_inverse_lt.
have hfg : KR (f \o g) := KR_comp_increasing hgc hinc hsurj hf.
rewrite (induced_daniell_value comp_locally_finite_variation hfg hab hzg).
rewrite (stieltjes_substitution (KR_continuous hf) hgc increasing_mono hh hab).
have hMM : - (M + 1) <= M + 1 by lra.
by rewrite /a /b !increasing_inverseK (induced_daniell_value hh hf hMM hz).
Qed.

(** Source for [stieltjes_image_induced_measures]: g_# maps the measures
    induced by h o g onto the measures induced by h, Federer 2.5.18(2), p.
    112 *)
Theorem stieltjes_image_induced_measures (psip psim : set R -> \bar R) :
  is_induced_measure_pair (h \o g) psip psim ->
  is_induced_measure_pair h (measure_pushforward g psip) (measure_pushforward g psim).
Proof.
move=> [P1 [Q1 [hP1 [hQ1 [hm1 [hn1 [hr1 [hs1 [hi1 hj1]]]]]]]]].
have hL := @compactly_supported_continuous_functions_lattice R R.
have hLp : is_function_lattice KRp := positive_lattice_is_lattice hL.
have hD := induced_daniell_is_daniell hh.
have hne : exists f, KR f by exists (fun _ => 0); exact: compactly_supported_zero_function.
have [P2 [Q2 [psip2 [psim2 [hP2 [hQ2 [hm2 [hn2 [hr2 [hs2 [hi2 [hj2 _]]]]]]]]]]]] :=
  daniell_integral_representation hL hD hne.
have hPc := positive_variation_comp induced_daniell_comp hP1 hP2.
have hQc : forall f, KRp f -> Q1 (f \o g) = Q2 f.
  apply: (positive_variation_comp (A1 := fun f => - induced_daniell (h \o g) f)
    (A2 := fun f => - induced_daniell h f)) hQ1 hQ2.
  by move=> f hf; rewrite induced_daniell_comp.
have heqp : measure_pushforward g psip = psip2.
  apply: daniell_cover_envelope_unique (envelope_image hPc _) _.
    exact (regular_representing_measure_envelope hLp hm1 hi1 hr1).
  exact (regular_representing_measure_envelope hLp hm2 hi2 hr2).
have heqm : measure_pushforward g psim = psim2.
  apply: daniell_cover_envelope_unique (envelope_image hQc _) _.
    exact (regular_representing_measure_envelope hLp hn1 hj1 hs1).
  exact (regular_representing_measure_envelope hLp hn2 hj2 hs2).
by rewrite heqp heqm; exists P2, Q2.
Qed.

End ImageMeasures.
