(** Federer (1969), 2.5.17, p. 111: consequences of the conditions (1) and
    (2) on the measures psi^+ and psi^- induced by g. If g is continuous at
    a and b, a < b, then g(b) - g(a) = psi^+{x : a <= x <= b} - psi^-{x : a
    <= x <= b}, the case f = 1 of the displayed integral identity; the
    single points of continuity of g have psi^+ and psi^- measure zero. The
    proof identifies psi^+{x : a < x < b} and psi^-{x : a < x < b} with the
    limits of the positive and negative variations of mu along the bump
    sequence of 2.5.17 suiting the open interval, through the envelope of
    2.5.2 and the Daniell continuity of the variations, and lets the
    Riemann-Stieltjes integrals of the bumps tend to g(b) - g(a), the
    variation of g near a and near b being small by the continuity of the
    arc length of 2.5.16. The induced measures are produced again by the
    representation theorem of 2.5.6 together with the conditions (1) and
    (2), so that the identities refer to the same measures. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealMetricBackground ExtendedRealBoundsUP ExtendedRealBounds
  ExtendedRealOrderLimit CurveVariationUP CurveArcLength CurveDiscontinuities CurveLipschitzFactor
  FunctionLatticeUP FunctionLatticeRegularityUP PositiveLatticeRegularity DaniellIntegralUP
  MonotoneDaniellIntegralUP DaniellVariationUP DaniellVariationBounds DaniellVariationFunctionals
  DaniellRepresentation DaniellCoverUP RegularDaniellEnvelope RealIntegralFunctionalUP MeasureUP
  MeasureBasic MeasureSplit MeasureIntegralUP SummableRealFunctionUP CompactSupportFunctionUP
  RealMetricCompleteness
  CompactSupportFunctionLattice StieltjesSums StieltjesIntegral StieltjesDaniellIntegral
  IntervalBumpFunctions StieltjesInducedMeasures StieltjesMonotone StieltjesSubstitution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [extended_increases_to_le_bound]: the limit of a
    nondecreasing sequence bounded by c is at most c, Federer 2.1.1,
    p. 51, supporting 2.5.17, p. 111. *)
Lemma extended_increases_to_le_bound (R : realType) (u : nat -> \bar R) (l c : \bar R) :
  extended_increases_to u l -> (forall n, (u n <= c)%E) -> (l <= c)%E.
Proof.
move=> [_ [hlow _]] hc; rewrite leNgt; apply/negP=> hlt.
have [N hN] := hlow c hlt.
by have := hN N (leqnn N); rewrite ltNge hc.
Qed.

(** Source for [measure_union_le]: subadditivity of a measure for two
    sets, Federer 2.1.2, p. 53, supporting 2.5.17, p. 111. *)
Lemma measure_union_le (R : realType) (X : choiceType) (mu : set X -> \bar R) (A B : set X) :
  is_measure mu -> (mu (A `|` B) <= mu A + mu B)%E.
Proof. by move=> hm; exact: (@measure_binary_cover R X mu hm (A `|` B) A B (fun x hx => hx)). Qed.

Section ContinuityPoints.
Variable R : realType.
Variable g : R -> R.
Hypothesis hg : curve_locally_finite_variation (g : R -> real_line_metric R).
Local Notation KR := (@compactly_supported_continuous_functions R R).
Local Notation KRp := (positive_function_lattice KR).
Local Notation mu := (induced_daniell g).
Local Notation s := (arc_length (g : R -> real_line_metric R)).

(** Source for [total_variation_arc_length]: V_t^u g = s(u) - s(t) for
    t <= u, Federer 2.5.16, p. 109, in the notation of 2.5.17. *)
Lemma total_variation_arc_length (t u : R) : t <= u -> total_variation g t u = s u - s t.
Proof. by move=> htu; rewrite /total_variation -(arc_length_increment hg htu). Qed.

(** Source for [variation_near_continuity]: the variation of g over
    small intervals around a point of continuity of g is small, by the
    continuity of s of Federer 2.5.16, p. 109, used in 2.5.17, p. 111. *)
Lemma variation_near_continuity (a e : R) :
  g @ a --> g a -> 0 < e ->
  exists2 d, 0 < d &
    forall t u, a - d < t -> t <= a -> a <= u -> u < a + d -> total_variation g t u < e.
Proof.
move=> hc he.
have hs : s @ a --> s a := (curve_continuous_iff hg (@real_line_metric_complete R) a).1 hc.
have he2 : 0 < e / 2 by lra.
have hn : nbhs a [set t | ball (s a) (e / 2) (s t)] by exact ((cvg_ballP _ _).1 hs (e / 2) he2).
have [d hd hb] := (nbhs_ballP a _).1 hn.
exists d=> // t u hat hta hau hua.
have hbt : ball a d t by rewrite /ball /= ger0_norm ?subr_ge0 //; lra.
have hbu : ball a d u by rewrite /ball /= ler0_norm ?subr_le0 //; lra.
have := hb t hbt; have := hb u hbu; rewrite /ball /= !ltr_norml.
rewrite (total_variation_arc_length (le_trans hta hau)).
by move=> /andP[h1 h2] /andP[h3 h4]; lra.
Qed.

(** Source for [induced_point_mass_zero]: a measure psi with
    psi{x : t < x < u} <= V_t^u g gives measure zero to every point of
    continuity of g, Federer 2.5.17, p. 111. *)
Lemma induced_point_mass_zero (psi : set R -> \bar R) (a : R) :
  is_measure psi -> (forall t u, t <= u -> (psi `]t, u[ <= (total_variation g t u)%:E)%E) ->
  g @ a --> g a -> psi [set a] = 0%E.
Proof.
move=> hm hb hc; apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
apply/lee_addgt0Pr=> e he; rewrite add0e.
have [d hd hv] := variation_near_continuity hc he.
have hsub : [set a] `<=` `]a - d / 2, a + d / 2[.
  by move=> x ->; rewrite /= in_itv /=; apply/andP; split; lra.
apply: le_trans (measure_mono hm hsub) _.
have hle : a - d / 2 <= a + d / 2 by lra.
apply: le_trans (hb _ _ hle) _; rewrite lee_fin; apply: ltW.
by apply: hv; lra.
Qed.

(** Source for [stieltjes_sum_eq_on_integrand]: the sum depends only on
    the values of the integrand at the terms of the sequence, Federer
    2.5.17, p. 110. *)
Lemma stieltjes_sum_eq_on_integrand (f1 f2 : R -> R) (w : seq R) :
  (forall x, x \in w -> f1 x = f2 x) -> stieltjes_sum f1 g w = stieltjes_sum f2 g w.
Proof.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|u [|t' rest]]] hsize heq //.
have hu : u \in t :: u :: t' :: rest by rewrite !inE eqxx orbT.
rewrite !stieltjes_sum_cons (heq u hu); congr (_ + _); apply: ih.
- by move: hsize; rewrite /= ltnS; exact: ltnW.
- by move=> x hx; apply: heq; rewrite 2!inE hx !orbT.
Qed.

(** Source for [stieltjes_integral_eq_on_integrand]: the integral over [a,
    b] depends only on the values of the integrand on [a, b], Federer
    2.5.17, p. 111 *)
Lemma stieltjes_integral_eq_on_integrand (f1 f2 : R -> R) (a b : R) :
  a <= b -> (forall x, a <= x <= b -> f1 x = f2 x) ->
  stieltjes_integral g f1 a b = stieltjes_integral g f2 a b.
Proof.
move=> hab heq; rewrite /stieltjes_integral.
have -> // : uniform_sums g f1 a b = uniform_sums g f2 a b.
apply/funext=> n; rewrite /uniform_sums; apply: stieltjes_sum_eq_on_integrand=> x hx.
exact: heq (tagged_partition_mem_bounds (uniform_partition_is n hab) hx).
Qed.

(** Source for [stieltjes_integral_constant]: int_a^b c dg = c [g(b) - g(a)],
    Federer 2.5.17, p. 111. *)
Lemma stieltjes_integral_constant (c a b : R) :
  a <= b -> stieltjes_integral g (fun _ => c) a b = c * (g b - g a).
Proof.
move=> hab; symmetry.
apply: (stieltjes_integral_unique hg (@cst_continuous _ _ c) hab)=> e he.
exists 1; split=> // w hw _.
by rewrite (stieltjes_sum_constant g c hw) subrr normr0.
Qed.

(** Source for [interval_bump_inner_one]: the n-th bump of 2.5.17 equals one
    on [a + 1/(n+1), b - 1/(n+1)], Federer 2.5.17, p. 111. *)
Lemma interval_bump_inner_one (a b : R) (n : nat) (x : R) :
  a + 1 / n.+1%:R <= x -> x <= b - 1 / n.+1%:R -> interval_bump a b n x = 1.
Proof.
move=> hax hxb; rewrite /interval_bump.
have hn : 0 < n.+1%:R :> R by rewrite ltr0n.
have hm : 1 / n.+1%:R <= Order.min (x - a) (b - x).
  by set q := (1 / n.+1%:R) in hax hxb *; rewrite le_min; apply/andP; split; lra.
have h1 : 1 <= n.+1%:R * Order.min (x - a) (b - x).
  apply: le_trans (ler_wpM2l (ltW hn) hm).
  by rewrite mulrC (mulfVK (lt0r_neq0 hn)) lexx.
by rewrite (min_l h1) max_r // ler01.
Qed.

(** Source for [bump_integral_near]: the integral of a bump over [a, b]
    differs from g(b) - g(a) by at most twice the variation of g near a
    and near b, Federer 2.5.17, p. 111. *)
Lemma bump_integral_near (a b : R) (n : nat) :
  a <= b -> 2 / n.+1%:R <= b - a ->
  `|stieltjes_integral g (interval_bump a b n) a b - (g b - g a)|
    <= 2 * (total_variation g a (a + 1 / n.+1%:R) + total_variation g (b - 1 / n.+1%:R) b).
Proof.
move=> hab hn.
have hn0 : 0 < 1 / n.+1%:R :> R by rewrite divr_gt0 // ltr0n.
have h2 : 2 / n.+1%:R = 2 * (1 / n.+1%:R) :> R by ring.
rewrite h2 in hn.
set q := (1 / n.+1%:R) in hn hn0 *.
set c1 := a + q; set c2 := b - q.
have hac1 : a <= c1 by rewrite /c1; lra.
have hc1c2 : c1 <= c2 by rewrite /c1 /c2; lra.
have hc2b : c2 <= b by rewrite /c2; lra.
have hcont : continuous (interval_bump a b n) := KR_continuous (interval_bump_member a b n).
rewrite -(stieltjes_integral_cat hg hcont hac1 (le_trans hc1c2 hc2b)).
rewrite -(stieltjes_integral_cat hg hcont hc1c2 hc2b).
have hmid : stieltjes_integral g (interval_bump a b n) c1 c2 = g c2 - g c1.
  rewrite -[g c2 - g c1]mul1r -(stieltjes_integral_constant 1 hc1c2).
  apply: stieltjes_integral_eq_on_integrand hc1c2 _ => x /andP[hx1 hx2].
  exact: interval_bump_inner_one hx1 hx2.
have hb1 : forall x, `|interval_bump a b n x| <= 1.
  by move=> x; rewrite ger0_norm ?interval_bump_ge0 //; exact: interval_bump_le1.
have hl := stieltjes_integral_bound hg hcont hac1 (fun x _ => hb1 x).
have hr := stieltjes_integral_bound hg hcont hc2b (fun x _ => hb1 x).
rewrite mul1r in hl hr.
have hga : `|g c1 - g a| <= total_variation g a c1.
  rewrite (total_variation_arc_length hac1).
  have := arc_length_distance_abs hg c1 a; rewrite real_line_metric_distanceE /= => h.
  have hsa : s a <= s c1 := arc_length_monotone hg hac1.
  by apply: le_trans h _; rewrite ger0_norm ?subr_ge0 ?lexx.
have hgb : `|g b - g c2| <= total_variation g c2 b.
  rewrite (total_variation_arc_length hc2b).
  have := arc_length_distance_abs hg b c2; rewrite real_line_metric_distanceE /= => h.
  have hsb : s c2 <= s b := arc_length_monotone hg hc2b.
  by apply: le_trans h _; rewrite ger0_norm ?subr_ge0 ?lexx.
rewrite hmid.
move: hl hr hga hgb; rewrite !ler_norml=> /andP[l1 l2] /andP[r1 r2] /andP[a1 a2] /andP[b1 b2].
by apply/andP; split; lra.
Qed.

(** Source for [bump_integral_limit]: the integrals of the bumps over
    [a, b] tend to g(b) - g(a) when g is continuous at a and b, Federer
    2.5.17, p. 111. *)
Lemma bump_integral_limit (a b e : R) :
  a < b -> g @ a --> g a -> g @ b --> g b -> 0 < e ->
  exists N : nat, forall n, (N <= n)%N ->
    `|stieltjes_integral g (interval_bump a b n) a b - (g b - g a)| < e.
Proof.
move=> hab hca hcb he.
have he4 : 0 < e / 4 by lra.
have [da hda hva] := variation_near_continuity hca he4.
have [db hdb hvb] := variation_near_continuity hcb he4.
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
apply: le_lt_trans (bump_integral_near (ltW hab) h2) _.
set q := (1 / n.+1%:R) in hsmall hpos *.
have hva' : total_variation g a (a + q) < e / 4.
  by apply: hva; lra.
have hvb' : total_variation g (b - q) b < e / 4.
  by apply: hvb; lra.
lra.
Qed.

(** Source for [bump_cost_open_interval]: for a monotone Daniell
    integral A on K(R)+ and the envelope measure psi of 2.5.2 associated
    with it, psi{x : a < x < b} is the supremum of the values of A on the
    bump sequence suiting the interval, Federer 2.5.2, p. 92, used in
    2.5.17, p. 111. *)
Lemma bump_cost_open_interval (A : (R -> R) -> R) (psi : set R -> \bar R) (a b : R) :
  is_monotone_daniell_integral KRp A -> is_daniell_cover_envelope KRp A psi ->
  is_extended_real_supremum [set z | exists n, z = (A (interval_bump a b n))%:E] (psi `]a, b[).
Proof.
move=> hA henv.
have hL := @compactly_supported_continuous_functions_lattice R R.
have hLp : is_function_lattice KRp := positive_lattice_is_lattice hL.
have hbump : forall n, KRp (interval_bump a b n).
  by move=> n; split; [exact: interval_bump_member | move=> x; exact: interval_bump_ge0].
pose S := [set z : \bar R | exists n, z = (A (interval_bump a b n))%:E].
have hcost : is_daniell_sequence_cost A (interval_bump a b) (extended_real_sup S).
  by split; [exact: extended_real_sup_upper | exact: extended_real_sup_least].
constructor.
- move=> z [n ->]; apply: (daniell_cover_greatest henv)=> f c [hf0 [hfmon hflim]] hc.
  pose h := fun k x => Order.min (interval_bump a b n x) (f k x).
  have hh : forall k, KRp (h k).
    by move=> k; exact: (function_lattice_minimum hLp (hbump n) (hf0 k).1).
  have hinc : real_functions_increase_to h (interval_bump a b n).
    move=> x; split.
    - move=> k m hkm; rewrite lee_fin /h le_min ge_min lexx /=.
      by rewrite ge_min (hfmon k m hkm x) orbT.
    split.
    - move=> r; case: r=> [r|hr|_]; last by exists 0%N=> k _; exact: ltNyr.
      + rewrite lte_fin=> hr.
        case: (boolP (a < x < b))=> [hx|hx].
        * have hx' : `]a, b[ x by rewrite /= in_itv.
          have hr1 : r < 1 := lt_le_trans hr (interval_bump_le1 a b n x).
          have [K hK] := hflim x hx' r hr1.
          exists K=> k hk; rewrite lte_fin /h lt_min hr /=.
          exact: lt_le_trans hK (hfmon K k hk x).
        * exists 0%N=> k _; rewrite lte_fin /h lt_min; apply/andP; split; first exact: hr.
          have hk0 := (hf0 k).2 x; move: hr; rewrite (interval_bump_zero n hx)=> hr0.
          exact: lt_le_trans hr0 hk0.
      + by move: hr; rewrite ltNge leey.
    - move=> r hr; exists 0%N=> k _; apply: le_lt_trans _ hr.
      by rewrite lee_fin /h ge_min lexx.
  have hlim := monotone_daniell_integral_increases hA hh (hbump n) hinc.
  apply: extended_increases_to_le_bound hlim _ => k.
  apply: le_trans _ (extended_real_supremum_upper hc (ex_intro _ k erefl)).
  rewrite lee_fin; apply: (monotone_daniell_integral_monotone hA (hh k) (hf0 k).1)=> x.
  by rewrite /h ge_min lexx orbT.
- move=> d hd.
  apply: le_trans (daniell_cover_lower henv (interval_bump_suiting (R := R) a b) hcost) _.
  exact: extended_real_sup_least.
Qed.

(** Source for [bump_values_monotone]: the values of a monotone Daniell
    integral on the bump sequence are nondecreasing, Federer 2.5.17,
    p. 111. *)
Lemma bump_values_monotone (A : (R -> R) -> R) (a b : R) (n m : nat) :
  is_monotone_daniell_integral KRp A -> (n <= m)%N ->
  A (interval_bump a b n) <= A (interval_bump a b m).
Proof.
move=> hA hnm.
have hbump : forall k, KRp (interval_bump a b k).
  by move=> k; split; [exact: interval_bump_member | move=> x; exact: interval_bump_ge0].
apply: (monotone_daniell_integral_monotone hA (hbump n) (hbump m))=> x.
exact (interval_bump_monotone a b x hnm).
Qed.

(** Source for [bump_values_approach]: the values of A on the bumps
    approach psi{x : a < x < b} from below, Federer 2.5.17, p. 111. *)
Lemma bump_values_approach (A : (R -> R) -> R) (psi : set R -> \bar R) (a b p e : R) :
  is_monotone_daniell_integral KRp A -> is_daniell_cover_envelope KRp A psi ->
  psi `]a, b[ = p%:E -> 0 < e ->
  exists N : nat, forall n, (N <= n)%N -> p - e < A (interval_bump a b n) <= p.
Proof.
move=> hA henv hp he.
have hsup := bump_cost_open_interval a b hA henv; rewrite hp in hsup.
have hup : forall n, A (interval_bump a b n) <= p.
  by move=> n; rewrite -lee_fin; exact: (extended_real_supremum_upper hsup (ex_intro _ n erefl)).
have [N hN] : exists N, p - e < A (interval_bump a b N).
  apply: contrapT=> hnot.
  have hall : forall n, A (interval_bump a b n) <= p - e.
    by move=> n; rewrite leNgt; apply/negP=> hlt; apply: hnot; exists n.
  have hle : (p%:E <= (p - e)%:E)%E.
    apply: (extended_real_supremum_least hsup)=> z [n ->]; rewrite lee_fin; exact: hall.
  by move: hle; rewrite lee_fin; lra.
exists N=> n hn; rewrite hup andbT.
exact: lt_le_trans hN (bump_values_monotone a b hA hn).
Qed.

(** Source for [induced_cost_bound]: condition (2) of Federer 2.5.17,
    p. 111, derived from the identification of the open interval measures
    with the limits of the variations along the bump sequence. *)
Lemma induced_cost_bound (P Q : (R -> R) -> R) (psip psim : set R -> \bar R) :
  is_daniell_positive_variation KR mu P -> is_daniell_negative_variation KR mu Q ->
  is_daniell_cover_envelope KRp P psip -> is_daniell_cover_envelope KRp Q psim ->
  forall a b : R, a <= b -> (psip `]a, b[ + psim `]a, b[ <= (total_variation g a b)%:E)%E.
Proof.
move=> hP hQ henvP henvQ a b hab.
have hL := @compactly_supported_continuous_functions_lattice R R.
have hD := induced_daniell_is_daniell hg.
have hAP := positive_variation_monotone_daniell hL hD hP.
have hAQ := negative_variation_monotone_daniell hL hD hQ.
pose SP := [set z : \bar R | exists n, z = (P (interval_bump a b n))%:E].
pose SQ := [set z : \bar R | exists n, z = (Q (interval_bump a b n))%:E].
have hcP : is_extended_real_supremum SP (extended_real_sup SP).
  by split; [exact: extended_real_sup_upper | exact: extended_real_sup_least].
have hcQ : is_extended_real_supremum SQ (extended_real_sup SQ).
  by split; [exact: extended_real_sup_upper | exact: extended_real_sup_least].
rewrite (extended_real_supremum_unique (bump_cost_open_interval a b hAP henvP) hcP).
rewrite (extended_real_supremum_unique (bump_cost_open_interval a b hAQ henvQ) hcQ).
have hbump : forall n, KRp (interval_bump a b n).
  by move=> n; split; [exact: interval_bump_member | move=> x; exact: interval_bump_ge0].
have hV : forall n, P (interval_bump a b n) + Q (interval_bump a b n) <= total_variation g a b.
  move=> n; apply: (induced_variations_interval_bound hg hP hQ hab (hbump n)).
  - by move=> x; exact: interval_bump_le1.
  - by move=> x; exact: interval_bump_support.
apply: extended_sup_sum_bound.
- by exists (P (interval_bump a b 0))%:E, 0%N.
- by exists (Q (interval_bump a b 0))%:E, 0%N.
- by move=> x [n ->]; exists (P (interval_bump a b n)).
- by move=> y [n ->]; exists (Q (interval_bump a b n)).
- move=> x y [n ->] [k ->]; rewrite -EFinD lee_fin.
  have hnk : (n <= maxn n k)%N := leq_maxl n k.
  have hkn : (k <= maxn n k)%N := leq_maxr n k.
  have h1 := bump_values_monotone a b hAP hnk.
  have h2 := bump_values_monotone a b hAQ hkn.
  by have := hV (maxn n k); lra.
Qed.

(** Source for [induced_increment_open]: g(b) - g(a) = psi^+{x : a < x < b}
    - psi^-{x : a < x < b} for a < b at points of continuity a, b of g,
    Federer 2.5.17, p. 111 *)
Lemma induced_increment_open (P Q : (R -> R) -> R) (psip psim : set R -> \bar R) (a b : R) :
  is_daniell_positive_variation KR mu P -> is_daniell_negative_variation KR mu Q ->
  is_daniell_cover_envelope KRp P psip -> is_daniell_cover_envelope KRp Q psim ->
  is_measure psip -> is_measure psim ->
  (forall t u, t <= u -> (psip `]t, u[ + psim `]t, u[ <= (total_variation g t u)%:E)%E) ->
  a < b -> g @ a --> g a -> g @ b --> g b ->
  (g b - g a)%:E = (psip `]a, b[ - psim `]a, b[)%E.
Proof.
move=> hP hQ henvP henvQ hmp hmm hbound hab hca hcb.
have hL := @compactly_supported_continuous_functions_lattice R R.
have hD := induced_daniell_is_daniell hg.
have hAP := positive_variation_monotone_daniell hL hD hP.
have hAQ := negative_variation_monotone_daniell hL hD hQ.
have hbump : forall n, KRp (interval_bump a b n).
  by move=> n; split; [exact: interval_bump_member | move=> x; exact: interval_bump_ge0].
have hV := hbound a b (ltW hab).
have hfinp : psip `]a, b[ \is a fin_num.
  rewrite fin_numElt; apply/andP; split.
  - exact: lt_le_trans (ltNyr 0) (measure_nonnegative hmp _).
  - apply: le_lt_trans (lee_paddr (measure_nonnegative hmm _) (lexx _)) _.
    exact: le_lt_trans hV (ltry _).
have hfinm : psim `]a, b[ \is a fin_num.
  rewrite fin_numElt; apply/andP; split.
  - exact: lt_le_trans (ltNyr 0) (measure_nonnegative hmm _).
  - apply: le_lt_trans (lee_paddl (measure_nonnegative hmp _) (lexx _)) _.
    exact: le_lt_trans hV (ltry _).
pose p := fine (psip `]a, b[); pose q := fine (psim `]a, b[).
have hp : psip `]a, b[ = p%:E by rewrite /p (fineK hfinp).
have hq : psim `]a, b[ = q%:E by rewrite /q (fineK hfinm).
rewrite hp hq -EFinB; congr (_%:E).
apply/eqP; rewrite -subr_eq0 -normr_eq0 eq_le normr_ge0 andbT.
apply/ler_addgt0Pr=> e he; rewrite add0r.
have he3 : 0 < e / 3 by lra.
have [N1 hN1] := bump_integral_limit hab hca hcb he3.
have [N2 hN2] := bump_values_approach hAP henvP hp he3.
have [N3 hN3] := bump_values_approach hAQ henvQ hq he3.
pose n := maxn (maxn N1 N2) N3.
have hn1 : (N1 <= n)%N := leq_trans (leq_maxl N1 N2) (leq_maxl _ N3).
have hn2 : (N2 <= n)%N := leq_trans (leq_maxr N1 N2) (leq_maxl _ N3).
have hn3 : (N3 <= n)%N := leq_maxr _ N3.
have h1 := hN1 n hn1.
have /andP[h2a h2b] := hN2 n hn2.
have /andP[h3a h3b] := hN3 n hn3.
have hmu : mu (interval_bump a b n) = P (interval_bump a b n) - Q (interval_bump a b n).
  exact (daniell_positive_negative_identity hL hD hP hQ (hbump n)).
have hval : mu (interval_bump a b n) = stieltjes_integral g (interval_bump a b n) a b.
  apply: (induced_daniell_value hg (interval_bump_member a b n) (ltW hab))=> x.
  exact: interval_bump_support.
rewrite -hval hmu in h1.
move: h1; rewrite ltr_norml=> /andP[h1a h1b].
by rewrite ler_norml; apply/andP; split; lra.
Qed.

(** Source for [measure_segment_open_interval]: a measure giving the end
    points measure zero takes the same value on the closed and on the
    open interval, Federer 2.1.2, p. 53, used in 2.5.17, p. 111. *)
Lemma measure_segment_open_interval (psi : set R -> \bar R) (a b : R) :
  is_measure psi -> psi [set a] = 0%E -> psi [set b] = 0%E -> psi `[a, b] = psi `]a, b[.
Proof.
move=> hm h0a h0b; apply/le_anti; apply/andP; split.
- have hsub : `[a, b] `<=` (`]a, b[ `|` [set a]) `|` [set b].
    move=> x; rewrite /= in_itv /= => /andP[hax hxb].
    move: hax; rewrite le_eqVlt => /orP[/eqP hax|hax]; first by left; right; rewrite /= hax.
    move: hxb; rewrite le_eqVlt => /orP[/eqP hxb|hxb]; first by right; rewrite /= hxb.
    by left; left; rewrite /= in_itv /= hax hxb.
  apply: le_trans (measure_mono hm hsub) _.
  apply: le_trans (measure_union_le _ _ hm) _; rewrite h0b adde0.
  by apply: le_trans (measure_union_le _ _ hm) _; rewrite h0a adde0.
- apply: (measure_mono hm)=> x; rewrite /= !in_itv /= => /andP[h1 h2].
  by apply/andP; split; exact: ltW.
Qed.

(** Source for [stieltjes_induced_measures_identities]: the measures psi^+
    and psi^- induced by g with the conditions (1) and (2) of Federer
    2.5.17, p. 111, the vanishing of psi^+ and psi^- at the points of
    continuity of g, and the identity g(b) - g(a) = psi^+{x : a <= x <= b} -
    psi^-{x : a <= x <= b} for a < b at points of continuity a and b of g,
    together with its open interval form *)
Theorem stieltjes_induced_measures_identities :
  exists (P Q : (R -> R) -> R) (psip psim : set R -> \bar R),
    is_daniell_positive_variation KR mu P /\ is_daniell_negative_variation KR mu Q /\
    is_measure psip /\ is_measure psim /\
    is_function_lattice_regular KR psip /\ is_function_lattice_regular KR psim /\
    (forall f, KR f -> exists u v : R,
      is_measure_integral psip (real_total_integrand f) u%:E /\
      is_measure_integral psim (real_total_integrand f) v%:E /\ mu f = u - v) /\
    (forall a b : R, a <= b -> (psip `]a, b[ + psim `]a, b[ <= (total_variation g a b)%:E)%E) /\
    (forall x : R, g @ x --> g x -> psip [set x] = 0%E /\ psim [set x] = 0%E) /\
    (forall a b : R, a < b -> g @ a --> g a -> g @ b --> g b ->
      (g b - g a)%:E = (psip `]a, b[ - psim `]a, b[)%E /\
      (g b - g a)%:E = (psip `[a, b] - psim `[a, b])%E).
Proof.
have hL := @compactly_supported_continuous_functions_lattice R R.
have hD := induced_daniell_is_daniell hg.
have hne : exists f, KR f by exists (fun _ => 0); exact: compactly_supported_zero_function.
have [P [Q [psip [psim [hP [hQ [hm [hn [hr [hs [hi [hj [hform _]]]]]]]]]]]]] :=
  daniell_integral_representation hL hD hne.
have hLp : is_function_lattice KRp := positive_lattice_is_lattice hL.
have hAP := positive_variation_monotone_daniell hL hD hP.
have hAQ := negative_variation_monotone_daniell hL hD hQ.
have henvP := regular_representing_measure_envelope hLp hm hi hr.
have henvQ := regular_representing_measure_envelope hLp hn hj hs.
have hbound := induced_cost_bound hP hQ henvP henvQ.
have hbp : forall t u, t <= u -> (psip `]t, u[ <= (total_variation g t u)%:E)%E.
  move=> t u htu; apply: le_trans _ (hbound t u htu).
  exact: lee_paddr (measure_nonnegative hn _) (lexx _).
have hbm : forall t u, t <= u -> (psim `]t, u[ <= (total_variation g t u)%:E)%E.
  move=> t u htu; apply: le_trans _ (hbound t u htu).
  exact: lee_paddl (measure_nonnegative hm _) (lexx _).
have hpoint : forall x : R, g @ x --> g x -> psip [set x] = 0%E /\ psim [set x] = 0%E.
  move=> x hc; split.
  - exact: induced_point_mass_zero hm hbp hc.
  - exact: induced_point_mass_zero hn hbm hc.
exists P, Q, psip, psim; split=> //; split=> //; split=> //; split=> //.
split; first exact ((@function_lattice_regular_positive_iff R R KR psip).1 hr).
split; first exact ((@function_lattice_regular_positive_iff R R KR psim).1 hs).
split=> //; split=> //; split=> // a b hab hca hcb.
have hopen := induced_increment_open hP hQ henvP henvQ hm hn hbound hab hca hcb.
split=> //.
have [h0a h0a'] := hpoint a hca.
have [h0b h0b'] := hpoint b hcb.
by rewrite (measure_segment_open_interval hm h0a h0b) (measure_segment_open_interval hn h0a' h0b').
Qed.

End ContinuityPoints.
