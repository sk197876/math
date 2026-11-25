(** Federer (1969), 2.5.17, p. 111: "It follows that, if g is a continuous
    function, then equality holds in (2)". For continuous g the identity
    g(u) - g(t) = psi^+{x : t < x < u} - psi^-{x : t < x < u} holds for all
    t < u, hence |g(u) - g(t)| <= psi^+{x : t < x < u} + psi^-{x : t < x <
    u}; the open intervals of a sequence a = t_1 <= ... <= t_(n+1) = b are
    disjoint and measurable for psi^+ and psi^-, so every chain sum of
    2.5.16 is at most psi^+{x : a < x < b} + psi^-{x : a < x < b}. The
    measurability of the open intervals follows from their description as
    increasing unions of strict levels of the bump functions of 2.5.17,
    which are measurable for every representing measure by 2.5.3. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealMetricBackground ExtendedRealBoundsUP ExtendedRealBounds
  CurveVariationUP CurveArcLength FunctionLatticeUP FunctionLatticeRegularityUP
  FunctionLatticeLevelFamilies FunctionLatticeLevelMeasurability PositiveLatticeRegularity
  DaniellIntegralUP MonotoneDaniellIntegralUP DaniellVariationUP DaniellVariationBounds
  DaniellVariationFunctionals DaniellRepresentation DaniellCoverUP RegularDaniellEnvelope
  RealIntegralFunctionalUP MeasureUP MeasureBasic MeasureFiniteAdditivity MeasureIntegralUP
  SummableRealFunctionUP CompactSupportFunctionUP CompactSupportFunctionLattice StieltjesSums
  StieltjesIntegral StieltjesDaniellIntegral IntervalBumpFunctions StieltjesInducedMeasures
  StieltjesContinuityPoints.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ContinuousIntegrator.
Variable R : realType.
Local Notation KR := (@compactly_supported_continuous_functions R R).
Local Notation KRp := (positive_function_lattice KR).

(** Source for [open_interval_increasing_level]: the open interval
    {x : c < x < d} is the increasing union of the strict levels
    {x : 1/2 < f_n(x)} of the bump functions f_n of 2.5.17, p. 111, a set
    of the family F1 of Federer 2.5.3, p. 94. *)
Lemma open_interval_increasing_level (c d : R) :
  function_lattice_increasing_levels KRp `]c, d[.
Proof.
exists (fun n => [set x | 2^-1 < interval_bump c d n x]); split; last split.
- move=> n; exists (interval_bump c d n), 2^-1; split; last first.
    by split; [rewrite invr_gt0 ltr0n | by []].
  split; last by move=> x; exact: interval_bump_ge0.
  by split; [exact: interval_bump_member | move=> x; exact: interval_bump_ge0].
- move=> n m hnm x /= hx; exact: lt_le_trans hx (interval_bump_monotone c d x hnm).
- apply/seteqP; split=> x.
  + rewrite /= in_itv /= => hx.
    have hhalf : (2^-1 : R) < 1 by rewrite invf_lt1 // ltr1n.
    have [n hn] := interval_bump_limit hx hhalf.
    by exists n.
  + move=> [n _ /= hn]; rewrite in_itv /=; apply: (interval_bump_support (n := n))=> h0.
    by move: hn; rewrite h0 ltNge invr_ge0 ler0n.
Qed.

(** Source for [open_interval_measurable]: the open intervals are
    measurable for every measure representing a functional on K(R)+,
    Federer 2.5.3, p. 94, used in 2.5.17, p. 111. *)
Lemma open_interval_measurable (psi : set R -> \bar R) (P : (R -> R) -> R) (c d : R) :
  is_measure psi -> is_real_integral_functional psi KRp P -> measure_measurable psi `]c, d[.
Proof.
move=> hm hi.
exact: (represented_lattice_increasing_level_measurable hm hi (open_interval_increasing_level c d)).
Qed.

(** Source for [open_interval_superadditive]: for a measure for which
    the open intervals are measurable,
    psi{t < x < t'} + psi{t' < x < t''} <= psi{t < x < t''} whenever
    t <= t' <= t'', Federer 2.1.2, p. 53, used in 2.5.17, p. 111. *)
Lemma open_interval_superadditive (psi : set R -> \bar R) (t t' t'' : R) :
  is_measure psi -> measure_measurable psi `]t, t'[ -> t <= t' -> t' <= t'' ->
  (psi `]t, t'[ + psi `]t', t''[ <= psi `]t, t''[)%E.
Proof.
move=> hm hmeas htt' ht't''.
have hdis : forall x, `]t, t'[ x -> `]t', t''[ x -> False.
  by move=> x; rewrite /= !in_itv /= => /andP[_ h1] /andP[h2 _]; move: (lt_trans h1 h2); rewrite ltxx.
rewrite -(measure_disjoint_union hmeas hdis); apply: (measure_mono hm)=> x.
rewrite /= !in_itv /= => -[/andP[h1 h2]|/andP[h1 h2]]; apply/andP; split=> //.
- exact: lt_le_trans h2 ht't''.
- exact: le_lt_trans htt' h1.
Qed.

Variable g : R -> R.
Hypothesis hg : curve_locally_finite_variation (g : R -> real_line_metric R).

(** Source for [increment_le_induced]: |g(u) - g(t)| is at most
    psi^+{t < x < u} + psi^-{t < x < u} when
    g(u) - g(t) = psi^+{t < x < u} - psi^-{t < x < u} and condition (2)
    of Federer 2.5.17, p. 111, holds. *)
Lemma increment_le_induced (psip psim : set R -> \bar R) (t u : R) :
  is_measure psip -> is_measure psim -> t <= u ->
  (psip `]t, u[ + psim `]t, u[ <= (total_variation g t u)%:E)%E ->
  (t < u -> (g u - g t)%:E = (psip `]t, u[ - psim `]t, u[)%E) ->
  (`|g u - g t|%:E <= psip `]t, u[ + psim `]t, u[)%E.
Proof.
move=> hmp hmm htu hV hid.
move: htu; rewrite le_eqVlt => /orP[/eqP <-|htu].
  by rewrite subrr normr0 adde_ge0 // measure_nonnegative.
have hp0 := measure_nonnegative hmp `]t, u[.
have hq0 := measure_nonnegative hmm `]t, u[.
have hpfin : psip `]t, u[ \is a fin_num.
  rewrite fin_numElt (lt_le_trans (ltNyr 0) hp0) /=.
  by apply: le_lt_trans (lee_paddr hq0 (lexx _)) _; exact: le_lt_trans hV (ltry _).
have hqfin : psim `]t, u[ \is a fin_num.
  rewrite fin_numElt (lt_le_trans (ltNyr 0) hq0) /=.
  by apply: le_lt_trans (lee_paddl hp0 (lexx _)) _; exact: le_lt_trans hV (ltry _).
have := hid htu; rewrite -(fineK hpfin) -(fineK hqfin) -EFinB -EFinD => -[->].
rewrite lee_fin; move: hp0 hq0; rewrite -(fineK hpfin) -(fineK hqfin) !lee_fin => hp0 hq0.
by rewrite ler_norml; apply/andP; split; lra.
Qed.

(** Source for [chain_sum_le_induced]: every chain sum of g over a
    nondecreasing sequence is at most
    psi^+{head < x < last} + psi^-{head < x < last}, under the
    increment identity at all pairs of points, Federer 2.5.17, p. 111. *)
Lemma chain_sum_le_induced (psip psim : set R -> \bar R) (P Q : (R -> R) -> R) (s : seq R) :
  is_measure psip -> is_measure psim ->
  is_real_integral_functional psip KRp P -> is_real_integral_functional psim KRp Q ->
  (forall t u, t <= u -> (psip `]t, u[ + psim `]t, u[ <= (total_variation g t u)%:E)%E) ->
  (forall t u, t < u -> (g u - g t)%:E = (psip `]t, u[ - psim `]t, u[)%E) ->
  sorted <=%O s ->
  ((chain_sum (g : R -> real_line_metric R) s)%:E
    <= psip `]head 0%R s, last 0%R s[ + psim `]head 0%R s, last 0%R s[)%E.
Proof.
move=> hmp hmm hip him hV hid.
elim: s=> [|t [|t' rest] ih] hs.
- by rewrite /= adde_ge0 // measure_nonnegative.
- by rewrite /= adde_ge0 // measure_nonnegative.
have htt' : t <= t' by move: hs=> /= /andP[].
have hs' : sorted <=%O (t' :: rest) by move: hs=> /= /andP[].
have ht'l : t' <= last t' rest.
  by have := sorted_le_last 0 hs' (mem_head t' rest); rewrite /=.
have hih := ih hs'; rewrite [head _ _]/= [last _ _]/= in hih.
rewrite chain_sum_cons EFinD real_line_metric_distanceE distrC [head _ _]/= [last _ _]/=.
have hinc := increment_le_induced hmp hmm htt' (hV t t' htt') (hid t t').
apply: le_trans (leeD hinc hih) _.
rewrite addeACA.
apply: leeD; apply: open_interval_superadditive=> //.
- exact: open_interval_measurable hmp hip.
- exact: open_interval_measurable hmm him.
Qed.

(** Source for [continuous_variation_le_induced]: for continuous g,
    V_a^b g <= psi^+{a < x < b} + psi^-{a < x < b}, the inequality
    opposite to (2), Federer 2.5.17, p. 111. *)
Lemma continuous_variation_le_induced (psip psim : set R -> \bar R) (P Q : (R -> R) -> R)
    (a b : R) :
  is_measure psip -> is_measure psim ->
  is_real_integral_functional psip KRp P -> is_real_integral_functional psim KRp Q ->
  (forall t u, t <= u -> (psip `]t, u[ + psim `]t, u[ <= (total_variation g t u)%:E)%E) ->
  (forall t u, t < u -> (g u - g t)%:E = (psip `]t, u[ - psim `]t, u[)%E) ->
  a <= b -> ((total_variation g a b)%:E <= psip `]a, b[ + psim `]a, b[)%E.
Proof.
move=> hmp hmm hip him hV hid hab.
rewrite /total_variation (fineK (curve_variation_fin_num hg hab)).
apply: extended_real_sup_least=> v [s [[hs [hsize [hh hl]]] ->]].
have hne : s <> [::] by case: s hsize {hs hh hl}.
have hh0 : head 0 s = a by rewrite -hh; case: s hne {hs hsize hh hl}.
have hl0 : last 0 s = b by rewrite -hl; exact: last_nonempty_default.
by have := chain_sum_le_induced hmp hmm hip him hV hid hs; rewrite hh0 hl0.
Qed.

(** Source for [stieltjes_continuous_induced_measures]: the measures
    psi^+ and psi^- induced by g with the conditions (1) and (2) of
    Federer 2.5.17, p. 111, the vanishing at points of continuity of g,
    the identity g(b) - g(a) = psi^+{a <= x <= b} - psi^-{a <= x <= b}
    at points of continuity a < b, and equality in (2) when g is
    continuous. *)
Theorem stieltjes_continuous_induced_measures :
  exists (P Q : (R -> R) -> R) (psip psim : set R -> \bar R),
    is_daniell_positive_variation KR (induced_daniell g) P /\
    is_daniell_negative_variation KR (induced_daniell g) Q /\
    is_measure psip /\ is_measure psim /\
    is_function_lattice_regular KR psip /\ is_function_lattice_regular KR psim /\
    (forall f, KR f -> exists u v : R,
      is_measure_integral psip (real_total_integrand f) u%:E /\
      is_measure_integral psim (real_total_integrand f) v%:E /\ induced_daniell g f = u - v) /\
    (forall a b : R, a <= b -> (psip `]a, b[ + psim `]a, b[ <= (total_variation g a b)%:E)%E) /\
    (forall x : R, g @ x --> g x -> psip [set x] = 0%E /\ psim [set x] = 0%E) /\
    (forall a b : R, a < b -> g @ a --> g a -> g @ b --> g b ->
      (g b - g a)%:E = (psip `]a, b[ - psim `]a, b[)%E /\
      (g b - g a)%:E = (psip `[a, b] - psim `[a, b])%E) /\
    (continuous g -> forall a b : R, a <= b ->
      (psip `]a, b[ + psim `]a, b[)%E = (total_variation g a b)%:E).
Proof.
have hL := @compactly_supported_continuous_functions_lattice R R.
have hD := induced_daniell_is_daniell hg.
have hne : exists f, KR f by exists (fun _ => 0); exact: compactly_supported_zero_function.
have [P [Q [psip [psim [hP [hQ [hm [hn [hr [hs [hi [hj [hform _]]]]]]]]]]]]] :=
  daniell_integral_representation hL hD hne.
have hLp : is_function_lattice KRp := positive_lattice_is_lattice hL.
have henvP := regular_representing_measure_envelope hLp hm hi hr.
have henvQ := regular_representing_measure_envelope hLp hn hj hs.
have hbound := induced_cost_bound hg hP hQ henvP henvQ.
have hbp : forall t u, t <= u -> (psip `]t, u[ <= (total_variation g t u)%:E)%E.
  move=> t u htu; apply: le_trans _ (hbound t u htu).
  exact: lee_paddr (measure_nonnegative hn _) (lexx _).
have hbm : forall t u, t <= u -> (psim `]t, u[ <= (total_variation g t u)%:E)%E.
  move=> t u htu; apply: le_trans _ (hbound t u htu).
  exact: lee_paddl (measure_nonnegative hm _) (lexx _).
have hpoint : forall x : R, g @ x --> g x -> psip [set x] = 0%E /\ psim [set x] = 0%E.
  by move=> x hc; split; [exact (induced_point_mass_zero hg hm hbp hc) |
    exact (induced_point_mass_zero hg hn hbm hc)].
have hincr : forall a b : R, a < b -> g @ a --> g a -> g @ b --> g b ->
    (g b - g a)%:E = (psip `]a, b[ - psim `]a, b[)%E /\
    (g b - g a)%:E = (psip `[a, b] - psim `[a, b])%E.
  move=> a b hab hca hcb.
  have hopen := induced_increment_open hg hP hQ henvP henvQ hm hn hbound hab hca hcb.
  split=> //.
  have [h0a h0a'] := hpoint a hca.
  have [h0b h0b'] := hpoint b hcb.
  by rewrite (measure_segment_open_interval hm h0a h0b) (measure_segment_open_interval hn h0a' h0b').
exists P, Q, psip, psim; split=> //; split=> //; split=> //; split=> //.
split; first exact ((@function_lattice_regular_positive_iff R R KR psip).1 hr).
split; first exact ((@function_lattice_regular_positive_iff R R KR psim).1 hs).
split=> //; split=> //; split=> //; split=> //.
move=> hc a b hab; apply/le_anti; rewrite hbound //=.
apply: (continuous_variation_le_induced hm hn hi hj hbound _ hab)=> t u htu.
exact: (hincr t u htu (hc t) (hc u)).1.
Qed.

End ContinuousIntegrator.
