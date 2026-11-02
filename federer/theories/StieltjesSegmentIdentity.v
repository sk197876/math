(** Federer (1969), 2.5.17, p. 111: from the conditions (1) and (2) it may
    be inferred that int_a^b f dg = int_{x : a <= x <= b} f dpsi^+ - int_{x
    : a <= x <= b} f dpsi^- provided g is continuous at a and b, a < b and f
    in K(R). For the bump functions b_n of 2.5.17 suiting {x : a < x < b},
    the products b_n f belong to K(R) and vanish outside {x : a < x < b}, so
    that int_a^b b_n f dg = mu(b_n f) = int b_n f dpsi^+ - int b_n f dpsi^-.
    As n tends to oo, the left side tends to int_a^b f dg, because b_n = 1
    on {x : a + 1/(n+1) <= x <= b - 1/(n+1)} and the variation of g near a
    and near b is small by the continuity of the arc length of 2.5.16; the
    integrals with respect to psi^+ and psi^- tend to the integrals of f
    over {x : a < x < b} by Lebesgue's bounded convergence theorem 2.4.9.
    The integrals over {x : a < x < b} and {x : a <= x <= b} agree because
    psi^+ and psi^- vanish at the points of continuity of g. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealMetricBackground ExtendedRealBoundsUP ExtendedRealBounds
  ExtendedRealOrderLimit ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPostcomposition
  PartialZeroExtension PartialExtendedOrderLoci PartialAbsolutePartsGraph
  PartialDominatedConvergence MeasureStepIntegralIdentification MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableZeroExtension
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralAlmostEquality
  MeasureBoundedConvergence MeasureSubsetIntegral SummableRealFunctionUP CompactMaximum
  RadonMeasureUP BorelRegularMeasureUP CurveVariationUP CurveArcLength FunctionLatticeUP
  FunctionLatticeLaws FunctionLatticeRegularityUP PositiveLatticeRegularity DaniellIntegralUP
  MonotoneDaniellIntegralUP DaniellVariationUP DaniellVariationBounds DaniellVariationFunctionals
  DaniellRepresentation DaniellCoverUP RegularDaniellEnvelope RealIntegralFunctionalUP
  CompactSupportFunctionUP CompactSupportFunctionLattice StieltjesSums StieltjesIntegral
  StieltjesDaniellIntegral IntervalBumpFunctions StieltjesInducedMeasures StieltjesContinuityPoints
  StieltjesContinuousIntegrator StieltjesBorelRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SegmentIdentity.
Variable R : realType.
Local Notation KR := (@compactly_supported_continuous_functions R R).
Local Notation KRp := (positive_function_lattice KR).

(** Source for [KR_product]: the product of two members of K(R) belongs
    to K(R), supporting the products b_n f in Federer 2.5.17, p. 111. *)
Lemma KR_product (h F : R -> R) : KR h -> KR F -> KR (fun x => h x * F x).
Proof.
move=> hh hF; split.
- have h1 := KR_continuous hh; have h2 := KR_continuous hF.
  have hc : continuous (fun x : R => h x * F x) by move=> x; exact: (cvgM (h1 x) (h2 x)).
  exact: hc.
- have [_ hc] := hh.
  rewrite /real_function_support.
  apply: (subclosed_compact (@closed_closure _ [set x | h x * F x <> 0]) hc).
  rewrite /real_function_support; apply: closureS=> x hx h0.
  by apply: hx; rewrite h0 mul0r.
Qed.

(** Source for [segment_value_bound]: a continuous real function is
    bounded on a segment, supporting the estimates of Federer 2.5.17,
    p. 111. *)
Lemma segment_value_bound (F : R -> R) (a b : R) :
  continuous F -> a <= b -> exists M, 0 <= M /\ forall x, a <= x <= b -> `|F x| <= M.
Proof.
move=> hF hab.
have hne : `[a, b] !=set0 by exists a; rewrite /= in_itv /= lexx hab.
have hcf : continuous (F : R -> R^o) := hF.
have hcn : continuous ((fun x => -1 * F x) : R -> R^o) := continuous_scale (c := -1) hF.
have [x1 [_ hmax1]] := continuous_compact_maximum hne (@segment_compact R a b) hcf.
have [x2 [_ hmax2]] := continuous_compact_maximum hne (@segment_compact R a b) hcn.
exists (`|F x1| + `|F x2|); split; first by rewrite addr_ge0.
move=> x hx; have hin : `[a, b] x by rewrite /= in_itv.
have h1 := hmax1 x hin; have h2 := hmax2 x hin.
rewrite !mulN1r in h2.
have e1 : F x1 <= `|F x1| := ler_norm _.
have e2 : - F x2 <= `|F x2| by rewrite -normrN; exact: ler_norm.
have := normr_ge0 (F x1); have := normr_ge0 (F x2) => n1 n2.
by rewrite ler_norml; apply/andP; split; lra.
Qed.

(** Source for [eventually_constant_order_limit]: an eventually constant
    sequence of extended real numbers converges to its eventual value,
    Federer 2.1.1, p. 51, used in 2.5.17, p. 111. *)
Lemma eventually_constant_order_limit (u : nat -> \bar R) (z : \bar R) (N : nat) :
  (forall n, (N <= n)%N -> u n = z) -> extended_order_limit u z.
Proof.
move=> hu; split.
- by move=> c hc; exists N=> n hn; rewrite hu.
- by move=> c hc; exists N=> n hn; rewrite hu.
Qed.

(** Source for [order_limit_real]: convergence in the order topology of
    the extended real numbers of a sequence of real numbers to a real
    limit, in the epsilon form, Federer 2.1.1, p. 51, used in 2.5.17,
    p. 111. *)
Lemma order_limit_real (u : nat -> R) (l e : R) :
  extended_order_limit (fun n => (u n)%:E) l%:E -> 0 < e ->
  exists N : nat, forall n, (N <= n)%N -> `|u n - l| < e.
Proof.
move=> [hlow hup] he.
have hle : ((l - e)%:E < l%:E)%E by rewrite lte_fin; lra.
have hue : (l%:E < (l + e)%:E)%E by rewrite lte_fin; lra.
have [N1 h1] := hlow _ hle.
have [N2 h2] := hup _ hue.
exists (maxn N1 N2)=> n hn.
have := h1 n (leq_trans (leq_maxl _ _) hn); have := h2 n (leq_trans (leq_maxr _ _) hn).
rewrite !lte_fin => hb ha.
by rewrite ltr_norml; apply/andP; split; lra.
Qed.

(** Source for [bump_eventually_one]: the bump functions of 2.5.17 take
    the value one at a point x with a < x < b from some index on,
    Federer 2.5.17, p. 111. *)
Lemma bump_eventually_one (a b x : R) :
  a < x < b -> exists N : nat, forall n, (N <= n)%N -> interval_bump a b n x = 1.
Proof.
move=> /andP[hax hxb].
have hd : 0 < Order.min (x - a) (b - x) by rewrite lt_min !subr_gt0 hax hxb.
have [N hN] := uniform_mesh_small (ler01 : (0 : R) <= 1) hd.
exists N=> n hn; have := hN n hn; rewrite subr0 lt_min => /andP[h1 h2].
apply: interval_bump_inner_one; set q := 1 / n.+1%:R in h1 h2 *; lra.
Qed.

(** Source for [bump_measure_limit]: for a measure psi representing a
    functional on K(R)+ and f in K(R), the integrals of b_n f with
    respect to psi converge to the integral of f over {x : a < x < b},
    by Lebesgue's bounded convergence theorem, Federer 2.4.9, p. 85, used
    in 2.5.17, p. 111. *)
Lemma bump_measure_limit (psi : set R -> \bar R) (P : (R -> R) -> R) (F : R -> R) (a b : R) :
  is_measure psi -> is_real_integral_functional psi KRp P -> KR F ->
  exists (c : nat -> R) (l : R),
    (forall n, is_measure_integral psi
      (real_total_integrand (fun x => interval_bump a b n x * F x)) (c n)%:E) /\
    is_measure_subset_integral psi `]a, b[ (real_total_integrand F) l%:E /\
    extended_order_limit (fun n => (c n)%:E) l%:E.
Proof.
move=> hm hi hF.
have hL := @compactly_supported_continuous_functions_lattice R R.
have hS := positive_representation_signed hm hi.
pose fs := fun n => real_total_integrand (fun x => interval_bump a b n x * F x).
pose gl := partial_function_zero_extension (0 : extended_real_line R) `]a, b[
  (real_total_integrand F).
pose H := fun x => Order.max (F x) (-1 * F x).
have hH : KR H := function_lattice_maximum hL hF (KR_scale (-1) hF).
have hsum : is_measure_summable psi (real_total_integrand H).
  by exists (P (fun x => Order.max (H x) 0) - P (fun x => Order.max (- H x) 0)); exact: hS H hH.
have hmf : forall n, is_measure_measurable_function psi (fs n).
  by move=> n; exact: (hS _ (KR_product (interval_bump_member a b n) hF)).1.
have hmg : is_measure_measurable_function psi gl.
  exact: (measurable_zero_extension hm _ (@open_interval_measurable R psi P a b hm hi)
    (hS F hF).1).
have hdom : forall n, measure_almost_everywhere psi
    (partial_extended_le_locus (partial_extended_function_absolute_value (fs n))
      (real_total_integrand H)).
  move=> n; rewrite /measure_almost_everywhere.
  suff -> : partial_extended_le_locus (partial_extended_function_absolute_value (fs n))
      (real_total_integrand H) = setT by rewrite setCT (measure_empty hm).
  apply/seteqP; split=> x // _.
  exists (`|interval_bump a b n x * F x|%:E), (H x)%:E; split.
    exists (interval_bump a b n x * F x)%:E; split; first exact/real_total_integrand_graph.
    by rewrite abse_EFin.
  split; first exact/real_total_integrand_graph.
  rewrite lee_fin normrM ger0_norm ?interval_bump_ge0 //.
  have hb : interval_bump a b n x * `|F x| <= `|F x|.
    rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r; first exact: normr_ge0.
    exact: interval_bump_le1.
  have hHx : `|F x| <= H x.
    rewrite /H /= le_max mulN1r; have [h|h] := lerP 0 (F x).
    - by rewrite ger0_norm // lexx.
    - by rewrite ltr0_norm // lexx orbT.
  exact: le_trans hb hHx.
have hconv : measure_almost_everywhere psi (partial_extended_convergence_locus fs gl).
  rewrite /measure_almost_everywhere.
  suff -> : partial_extended_convergence_locus fs gl = setT by rewrite setCT (measure_empty hm).
  apply/seteqP; split=> x // _.
  have [hx|hx] := boolP (a < x < b).
  - have [N hN] := bump_eventually_one hx.
    exists (fun n => (interval_bump a b n x * F x)%:E), (F x)%:E; split.
      by move=> n; exact/real_total_integrand_graph.
    have hxA : `]a, b[ x by rewrite /= in_itv.
    split.
      by apply/(partial_function_zero_extension_on _ _ _ hxA); exact/real_total_integrand_graph.
    by apply: (eventually_constant_order_limit (N := N))=> n hn; rewrite (hN n hn) mul1r.
  - exists (fun n => (interval_bump a b n x * F x)%:E), 0%E; split.
      by move=> n; exact/real_total_integrand_graph.
    have hxA : ~ `]a, b[ x by rewrite /= in_itv; exact/negP.
    split; first by apply/(partial_function_zero_extension_off _ _ _ hxA).
    by apply: (eventually_constant_order_limit (N := 0%N))=> n _; rewrite (interval_bump_zero n hx) mul0r.
have [c [e0 [l [hc [hl [_ [_ hlim]]]]]]] :=
  @measure_bounded_convergence R R psi hm fs gl (real_total_integrand H) hsum hmf hmg hdom hconv.
by exists c, l.
Qed.

(** Source for [segment_subset_integral]: a measure vanishing at a and
    at b has the same integrals over {x : a < x < b} and over
    {x : a <= x <= b}, Federer 2.4.10, p. 85, used in 2.5.17, p. 111. *)
Lemma segment_subset_integral (psi : set R -> \bar R) (F : R -> R) (a b : R) (l : \bar R) :
  is_measure psi -> psi [set a] = 0%E -> psi [set b] = 0%E ->
  is_measure_subset_integral psi `]a, b[ (real_total_integrand F) l ->
  is_measure_subset_integral psi `[a, b] (real_total_integrand F) l.
Proof.
move=> hm h0a h0b hl.
apply: (measure_integral_almost_equal hm hl).
rewrite /measure_almost_equal /measure_almost_everywhere.
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
have hsub : ~` partial_function_agreement
    (partial_function_zero_extension (0 : extended_real_line R) `]a, b[ (real_total_integrand F))
    (partial_function_zero_extension (0 : extended_real_line R) `[a, b] (real_total_integrand F))
    `<=` [set a] `|` [set b].
  move=> x hx; apply: contrapT=> hab'; apply: hx.
  have hxa : x <> a by move=> e; apply: hab'; left.
  have hxb : x <> b by move=> e; apply: hab'; right.
  have [hin|hout] := pselect (`]a, b[ x).
  - have hin' : `[a, b] x.
      by move: hin; rewrite /= !in_itv /= => /andP[h1 h2]; rewrite (ltW h1) (ltW h2).
    exists (F x)%:E; split.
    + by apply/(partial_function_zero_extension_on _ _ _ hin); exact/real_total_integrand_graph.
    + by apply/(partial_function_zero_extension_on _ _ _ hin'); exact/real_total_integrand_graph.
  - have hout' : ~ `[a, b] x.
      move=> hc; apply: hout; move: hc; rewrite /= !in_itv /= => /andP[h1 h2].
      rewrite !lt_neqAle h1 h2 !andbT; apply/andP; split; apply/eqP=> e.
      + exact: hxa (esym e).
      + exact: hxb e.
    exists 0%E; split.
    + by apply/(partial_function_zero_extension_off _ _ _ hout).
    + by apply/(partial_function_zero_extension_off _ _ _ hout').
apply: le_trans (measure_mono hm hsub) _.
by rewrite (measure_null_union hm h0a h0b).
Qed.

(** Source for [split_difference_estimate]: the elementary estimate
    |(A1 + (C + B1)) - (A2 + (C + B2))| <= 2 V1 + 2 V2 for
    |A1|, |A2| <= V1 and |B1|, |B2| <= V2, supporting the comparison of
    integrals split at two points in Federer 2.5.17, p. 111. *)
Lemma split_difference_estimate (A1 A2 B1 B2 C V1 V2 : R) :
  `|A1| <= V1 -> `|A2| <= V1 -> `|B1| <= V2 -> `|B2| <= V2 ->
  `|A1 + (C + B1) - (A2 + (C + B2))| <= 2 * V1 + 2 * V2.
Proof.
rewrite !ler_norml => /andP[l1 l2] /andP[l3 l4] /andP[r1 r2] /andP[r3 r4].
by apply/andP; split; lra.
Qed.

Variable g : R -> R.
Hypothesis hg : curve_locally_finite_variation (g : R -> real_line_metric R).
Local Notation mu := (induced_daniell g).

(** Source for [bump_product_integral_near]: the Riemann-Stieltjes
    integrals of b_n f and of f over [a, b] differ by at most
    2 M (V_a^{a + 1/(n+1)} g + V_{b - 1/(n+1)}^b g) when |f| <= M on
    [a, b], Federer 2.5.17, p. 111. *)
Lemma bump_product_integral_near (F : R -> R) (a b M : R) (n : nat) :
  continuous F -> a <= b -> 2 / n.+1%:R <= b - a -> (forall x, a <= x <= b -> `|F x| <= M) ->
  `|stieltjes_integral g (fun x => interval_bump a b n x * F x) a b - stieltjes_integral g F a b|
    <= 2 * (M * total_variation g a (a + 1 / n.+1%:R))
       + 2 * (M * total_variation g (b - 1 / n.+1%:R) b).
Proof.
move=> hF hab hn hM.
have hn0 : 0 < 1 / n.+1%:R :> R by rewrite divr_gt0 // ltr0n.
have h2 : 2 / n.+1%:R = 2 * (1 / n.+1%:R) :> R by ring.
rewrite h2 in hn.
set q := (1 / n.+1%:R) in hn hn0 *.
set c1 := a + q; set c2 := b - q.
have hac1 : a <= c1 by rewrite /c1; lra.
have hc1c2 : c1 <= c2 by rewrite /c1 /c2; lra.
have hc2b : c2 <= b by rewrite /c2; lra.
have hbc : continuous (interval_bump a b n) := KR_continuous (interval_bump_member a b n).
have hpc : continuous (fun x : R => interval_bump a b n x * F x).
  by move=> x; exact: (cvgM (hbc x) (hF x)).
rewrite -(stieltjes_integral_cat hg hpc hac1 (le_trans hc1c2 hc2b)).
rewrite -(stieltjes_integral_cat hg hpc hc1c2 hc2b).
rewrite -(stieltjes_integral_cat hg hF hac1 (le_trans hc1c2 hc2b)).
rewrite -(stieltjes_integral_cat hg hF hc1c2 hc2b).
have hmid : stieltjes_integral g (fun x => interval_bump a b n x * F x) c1 c2
    = stieltjes_integral g F c1 c2.
  apply: stieltjes_integral_eq_on_integrand hc1c2 _ => x /andP[hx1 hx2].
  by rewrite (interval_bump_inner_one hx1 hx2) mul1r.
rewrite hmid.
have hbound : forall x, a <= x <= b -> `|interval_bump a b n x * F x| <= M.
  move=> x hx; rewrite normrM.
  have hb1 : `|interval_bump a b n x| <= 1.
    by rewrite ger0_norm ?interval_bump_ge0 // interval_bump_le1.
  have hFx := hM x hx.
  rewrite -[M]mul1r; apply: ler_pM=> //; exact: normr_ge0.
have hA : forall x, a <= x <= c1 -> `|interval_bump a b n x * F x| <= M.
  by move=> x /andP[hx1 hx2]; apply: hbound; apply/andP; split; lra.
have hB : forall x, c2 <= x <= b -> `|interval_bump a b n x * F x| <= M.
  by move=> x /andP[hx1 hx2]; apply: hbound; apply/andP; split; lra.
have hFA : forall x, a <= x <= c1 -> `|F x| <= M.
  by move=> x /andP[hx1 hx2]; apply: hM; apply/andP; split; lra.
have hFB : forall x, c2 <= x <= b -> `|F x| <= M.
  by move=> x /andP[hx1 hx2]; apply: hM; apply/andP; split; lra.
have hl1 := stieltjes_integral_bound hg hpc hac1 hA.
have hl2 := stieltjes_integral_bound hg hF hac1 hFA.
have hr1 := stieltjes_integral_bound hg hpc hc2b hB.
have hr2 := stieltjes_integral_bound hg hF hc2b hFB.
exact (@split_difference_estimate _ _ _ _ _ _ _ hl1 hl2 hr1 hr2).
Qed.

(** Source for [bump_product_integral_limit]: the Riemann-Stieltjes
    integrals of b_n f over [a, b] tend to int_a^b f dg when g is
    continuous at a and b, Federer 2.5.17, p. 111. *)
Lemma bump_product_integral_limit (F : R -> R) (a b e : R) :
  continuous F -> a < b -> g @ a --> g a -> g @ b --> g b -> 0 < e ->
  exists N : nat, forall n, (N <= n)%N ->
    `|stieltjes_integral g (fun x => interval_bump a b n x * F x) a b
      - stieltjes_integral g F a b| < e.
Proof.
move=> hF hab hca hcb he.
have [M [hM0 hM]] := segment_value_bound hF (ltW hab).
have hM1 : 0 < 4 * (M + 1) by apply: mulr_gt0=> //; lra.
pose e' := e / (4 * (M + 1)).
have he' : 0 < e' by rewrite /e' divr_gt0.
have hfe : 4 * (M * e') + 4 * e' = e.
  have : e' * (4 * (M + 1)) = e by rewrite /e' mulfVK // lt0r_neq0.
  by move=> <-; ring.
have [da hda hva] := variation_near_continuity hg hca he'.
have [db hdb hvb] := variation_near_continuity hg hcb he'.
pose d := Order.min (Order.min da db) ((b - a) / 2).
have hd : 0 < d by rewrite !lt_min hda hdb; apply/andP; split=> //; lra.
have hdda : d <= da by rewrite /d ge_min ge_min lexx.
have hddb : d <= db by rewrite /d ge_min ge_min lexx orbT.
have hdab : d <= (b - a) / 2 by rewrite /d ge_min lexx orbT.
have [N hN] := uniform_mesh_small (ler01 : (0 : R) <= 1) hd.
exists N=> n hn; have := hN n hn; rewrite subr0=> hsmall.
have hpos : 0 < 1 / n.+1%:R :> R by rewrite divr_gt0 // ltr0n.
have h2 : 2 / n.+1%:R <= b - a.
  have -> : 2 / n.+1%:R = 2 * (1 / n.+1%:R) :> R by ring.
  by set q := (1 / n.+1%:R) in hsmall hpos *; lra.
apply: le_lt_trans (bump_product_integral_near hF (ltW hab) h2 hM) _.
set q := (1 / n.+1%:R) in hsmall hpos *.
have hva' : total_variation g a (a + q) < e' by apply: hva; lra.
have hvb' : total_variation g (b - q) b < e' by apply: hvb; lra.
have hp1 : M * total_variation g a (a + q) <= M * e' by apply: ler_wpM2l=> //; exact: ltW.
have hp2 : M * total_variation g (b - q) b <= M * e' by apply: ler_wpM2l=> //; exact: ltW.
by lra.
Qed.

(** Source for [segment_identity_core]: the identity
    int_a^b f dg = int_{a <= x <= b} f dpsi^+ - int_{a <= x <= b} f dpsi^-
    of Federer 2.5.17, p. 111, for measures psi^+ and psi^- representing
    the positive and negative variations of mu on K(R)+, satisfying (1)
    and vanishing at the points of continuity of g. *)
Lemma segment_identity_core (P Q : (R -> R) -> R) (psip psim : set R -> \bar R) :
  is_measure psip -> is_measure psim ->
  is_real_integral_functional psip KRp P -> is_real_integral_functional psim KRp Q ->
  (forall f, KR f -> exists u v : R,
      is_measure_integral psip (real_total_integrand f) u%:E /\
      is_measure_integral psim (real_total_integrand f) v%:E /\ mu f = u - v) ->
  (forall x, g @ x --> g x -> psip [set x] = 0%E /\ psim [set x] = 0%E) ->
  forall (F : R -> R) (a b : R), KR F -> a < b -> g @ a --> g a -> g @ b --> g b ->
    exists u v : R,
      is_measure_subset_integral psip `[a, b] (real_total_integrand F) u%:E /\
      is_measure_subset_integral psim `[a, b] (real_total_integrand F) v%:E /\
      stieltjes_integral g F a b = u - v.
Proof.
move=> hmp hmm hip him hform hpoint F a b hF hab hca hcb.
have [cp [lp [hcp [hlp hlimp]]]] := bump_measure_limit a b hmp hip hF.
have [cm [lm [hcm [hlm hlimm]]]] := bump_measure_limit a b hmm him hF.
have hseq : forall n,
    stieltjes_integral g (fun x => interval_bump a b n x * F x) a b = cp n - cm n.
  move=> n.
  have hbF := KR_product (interval_bump_member a b n) hF.
  have [u [v [hu [hv he]]]] := hform _ hbF.
  have [e1] := measure_integral_unique hu (hcp n).
  have [e2] := measure_integral_unique hv (hcm n).
  have hz : forall x, interval_bump a b n x * F x <> 0 -> a < x < b.
    by move=> x hx; apply: (interval_bump_support (n := n))=> h0; apply: hx; rewrite h0 mul0r.
  by rewrite -(induced_daniell_value hg hbF (ltW hab) hz) he e1 e2.
have hS : stieltjes_integral g F a b = lp - lm.
  apply/eqP; rewrite -subr_eq0 -normr_eq0 eq_le normr_ge0 andbT.
  apply/ler_addgt0Pr=> e he; rewrite add0r.
  have he3 : 0 < e / 3 by lra.
  have [N1 hN1] := bump_product_integral_limit (KR_continuous hF) hab hca hcb he3.
  have [N2 hN2] := order_limit_real hlimp he3.
  have [N3 hN3] := order_limit_real hlimm he3.
  pose n := maxn (maxn N1 N2) N3.
  have h1 := hN1 n (leq_trans (leq_maxl N1 N2) (leq_maxl _ N3)).
  have h2 := hN2 n (leq_trans (leq_maxr N1 N2) (leq_maxl _ N3)).
  have h3 := hN3 n (leq_maxr _ N3).
  rewrite hseq in h1.
  move: h1 h2 h3; rewrite !ltr_norml => /andP[a1 a2] /andP[b1 b2] /andP[c1 c2].
  by rewrite ler_norml; apply/andP; split; lra.
have [h0a h0a'] := hpoint a hca.
have [h0b h0b'] := hpoint b hcb.
exists lp, lm; split; last split=> //.
- exact: segment_subset_integral hmp h0a h0b hlp.
- exact: segment_subset_integral hmm h0a' h0b' hlm.
Qed.

(** Source for [stieltjes_segment_identity]: the measures psi^+ and psi^-
    induced by g, Radon and Borel regular, with the conditions (1) and
    (2) of Federer 2.5.17, p. 111, and the identity
    int_a^b f dg = int_{x : a <= x <= b} f dpsi^+ - int_{x : a <= x <= b} f dpsi^-
    whenever f in K(R), a < b and g is continuous at a and b. *)
Theorem stieltjes_segment_identity :
  exists (P Q : (R -> R) -> R) (psip psim : set R -> \bar R),
    is_daniell_positive_variation KR mu P /\ is_daniell_negative_variation KR mu Q /\
    is_measure psip /\ is_measure psim /\
    is_radon_measure psip /\ is_radon_measure psim /\
    is_borel_regular_measure psip /\ is_borel_regular_measure psim /\
    is_function_lattice_regular KR psip /\ is_function_lattice_regular KR psim /\
    (forall f, KR f -> exists u v : R,
      is_measure_integral psip (real_total_integrand f) u%:E /\
      is_measure_integral psim (real_total_integrand f) v%:E /\ mu f = u - v) /\
    (forall a b : R, a <= b -> (psip `]a, b[ + psim `]a, b[ <= (total_variation g a b)%:E)%E) /\
    (forall x : R, g @ x --> g x -> psip [set x] = 0%E /\ psim [set x] = 0%E) /\
    (forall (f : R -> R) (a b : R), KR f -> a < b -> g @ a --> g a -> g @ b --> g b ->
      exists u v : R,
        is_measure_subset_integral psip `[a, b] (real_total_integrand f) u%:E /\
        is_measure_subset_integral psim `[a, b] (real_total_integrand f) v%:E /\
        stieltjes_integral g f a b = u - v).
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
have [hradp hborp] := positive_regular_radon hm hi hr.
have [hradm hborm] := positive_regular_radon hn hj hs.
exists P, Q, psip, psim; do 8!(split=> //).
split; first exact ((@function_lattice_regular_positive_iff R R KR psip).1 hr).
split; first exact ((@function_lattice_regular_positive_iff R R KR psim).1 hs).
split=> //; split=> //; split=> //.
exact: segment_identity_core hm hn hi hj hform hpoint.
Qed.

End SegmentIdentity.
