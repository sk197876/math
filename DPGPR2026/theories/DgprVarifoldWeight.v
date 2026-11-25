(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    thm:MS: the part of its proof which concerns the weight ‖V‖ of a
    rectifiable varifold V ∈ RV_k(R^n) with ‖V‖(R^n) < ∞ (Allard 3.1
    and 3.5).

    The set M = R^n ∩ { x : 1 ≤ Θ^k(‖V‖, x) < ∞ } of thm:MS is
    [dgpr_MS_set k W] for W = ‖V‖, with the density Θ^k of Federer
    2.10.19 as a partial function. The inequality (eq:MS:HM),
    H^k(M) ≤ ‖V‖(R^n), is [dgpr_MS_HM]; as in the blueprint, it follows
    from Federer 2.10.19(3) and H^k ≤ S^k
    ([finite_upper_density_hausdorff_bound]).

    Suppose moreover that Θ^k(‖V‖, x) ≥ 1 for ‖V‖ almost all x. Then
    ‖V‖(R^n ∖ M) = 0 ([dgpr_MS_set_full]). The blueprint asserts that M
    is a Borel set; this assertion is not formalised. Instead, the Borel
    regularity of ‖V‖ yields a Borel set M' ⊆ M with ‖V‖(R^n ∖ M') = 0
    ([dgpr_MS_borel_part]), and the data of mr:hypotheses_main are
    formed with M' in place of M (docs/divergences.md). For such a set
    M' let θ(x) = Θ^{*k}(‖V‖, x) for x ∈ M' and θ(x) = 0 for
    x ∈ R^n ∖ M' ([dgpr_MS_density]). Then θ is a Borel function,
    Θ^k(‖V‖, x) = θ(x) ≥ 1 for x ∈ M', ‖V‖ = (H^k ⌞ M') ⌞ θ
    ([dgpr_MS_weight_representation]), θ is H^k ⌞ M' summable
    ([dgpr_MS_density_summable]), and M' is countably (H^k, k)
    rectifiable ([dgpr_MS_rectifiable]) with H^k(M') < ∞
    ([dgpr_MS_borel_part_finite]). The representation of ‖V‖ combines
    Allard 3.5(1)(b), ‖V‖ = H^k ⌞ Θ^k(‖V‖, ·), with the equation
    Θ^{*k}(‖V‖, x) = 0 for H^k almost all x ∈ R^n ∖ M', which follows
    from Federer 2.10.19(3) and ‖V‖(R^n ∖ M') = 0. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  cardinality reals topology constructive_ereal ring lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates InnerNorm
  InnerMetric RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPreimages PartialZeroExtension PartialExtendedOrderLoci MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic MeasureRestriction MeasureDensityUP MeasureDensity
  MeasureSubsetIntegral MeasureIntegralUP MeasurableFunctionUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureBoundGraphEquivalence MeasureNonnegativeIntegral
  MeasureStepIntegralIdentification SummableRealFunctionUP RadonMeasureUP RadonBorelRegularity
  BorelRegularMeasureUP TopologicalBorel BorelFunctionUP BorelFunctionBasic
  ExtendedFiniteProjectionBorel StructureBorelOrderCriterion HausdorffMeasure MetricDensities
  MetricDensityZero MetricDensityNumericalBounds MetricDensityCutoffOpen PositiveRadiusLimits
  PositiveRadiusReciprocalCutoffs FiniteUpperDensityHausdorffBound DensitySupportedRestriction
  RectifiableSetUP CountablyMeasureRectifiableOperations EuclideanClosedBallCompact NonnegativeSum
  NonnegativeSumSupport MetricClosedBalls MeasureDensityTransfer.
From Allard Require Import AllardGrassmann AllardVarifolds AllardRectifiableVarifolds
  AllardTangentMeasurability AllardRectifiableSum AllardRectifiableStructure.
From DPGPR Require Import DgprMainHypotheses.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dgpr_small_reciprocal]: the Archimedean property of R,
    used in the proof of blueprint thm:MS: for 0 < s there is j ∈ N
    with 1/(j + 1) < s. Supporting lemma. *)
Lemma dgpr_small_reciprocal (R : realType) (s : R) : 0 < s -> exists j : nat, (j.+1%:R)^-1 < s.
Proof.
move=> hs; set j := Num.bound s^-1; exists j.
have h1 : s^-1 < j.+1%:R.
  apply: lt_trans (archi_boundP _) _; first by rewrite invr_ge0 ltW.
  by rewrite ltr_nat.
have hj : 0 < j.+1%:R :> R by rewrite ltr0n.
have e : s = (s^-1)^-1 by rewrite invrK.
rewrite [X in _ < X]e ltf_pV2 ?posrE ?invr_gt0 //.
Qed.

(** Source for [dgpr_borel_setI]: Federer 2.2.1, pp. 59–60: the Borel
    family is closed under complements and countable unions; hence the
    intersection of two Borel sets is a Borel set. Supporting lemma. *)
Lemma dgpr_borel_setI (T : topologicalType) (A B : set T) :
  borel_set A -> borel_set B -> borel_set (A `&` B).
Proof.
move=> hA hB.
have -> : A `&` B = ~` (~` A `|` ~` B).
  apply/seteqP; split=> x.
  - by move=> [ha hb] [h|h]; [exact: h ha|exact: h hb].
  - move=> h; split; apply: contrapT=> h'; apply: h; [left|right]; exact: h'.
apply: borel_set_complement; apply: borel_setU; exact: borel_set_complement.
Qed.

Section VarifoldWeight.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation RnM := (inner_metric_space hBn).
Local Notation HK := (@hausdorff_measure R RnM k).
Local Notation GB := (grassmann_bundle R n k).

(** Source for [dgpr_MS_set]: blueprint thm:MS, the set
    M = R^n ∩ { x : 1 ≤ Θ^k(W, x) < ∞ } for a measure W over R^n, with
    the density Θ^k(W, x) of Federer 2.10.19, p. 181, a partial function
    of x: the point x belongs to M if and only if Θ^k(W, x) exists and
    is a real number t with 1 ≤ t. Definition. *)
Definition dgpr_MS_set (W : set RnM -> \bar R) : set RnM :=
  [set x | exists t : R, 1 <= t /\ partial_function_graph (@metric_density R RnM k W) x t%:E].

(** Source for [dgpr_borel_restrict_measurable]: Federer 2.2.3, p. 61,
    and 2.3.2, p. 73: since H^k is Borel regular (Federer 2.10.1), every
    Borel function on R^n is H^k ⌞ A measurable for each A ⊆ R^n.
    Supporting lemma. *)
Lemma dgpr_borel_restrict_measurable (A : set RnM) (Y : topologicalType) (f : RnM -> Y) :
  is_borel_function f -> is_measure_measurable_function (measure_restrict HK A) (partial_function_total f).
Proof.
move=> hf; have [hHm hHr] := @hausdorff_measure_laws R n k.
have hrm := measure_restrict_is_measure hHm A.
constructor.
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hrm.
- move=> U hU; rewrite partial_function_total_preimage.
  apply: measure_restrict_measurable.
  exact: (@borel_regular_borel_measurable R RnM HK hHm hHr _ (hf U hU)).
Qed.

Variable V : set GB -> \bar R.
Hypothesis hV : is_rectifiable_varifold V.
Hypothesis hVf : (V setT < +oo)%E.
Local Notation W := (varifold_weight V).
Local Notation upper := (@upper_metric_density R RnM k W).

(** Source for [dgpr_weight_laws]: Allard 3.1, p. 430, and Federer
    2.2.5, p. 62: the weight ‖V‖ of a varifold V is a Radon measure over
    R^n, hence Borel regular; moreover ‖V‖(R^n) = V(G_k(R^n)) < ∞ by
    hypothesis. Supporting lemma. *)
Lemma dgpr_weight_laws :
  [/\ is_measure W, is_radon_measure W, is_borel_regular_measure W & (W setT < +oo)%E].
Proof.
have [hm hr] := allard_3_1 hV.1.
split=> //; exact: radon_borel_regular hm hr.
Qed.

(** Source for [dgpr_weight_null_hausdorff_null]: Federer 2.10.19(3),
    p. 181, with H^k ≤ S^k (Federer 2.10.6), as used in the proof of
    blueprint thm:MS: if 0 < t, ‖V‖(B) = 0 and Θ^{*k}(‖V‖, x) > t for
    x ∈ B, then H^k(B) = 0. Supporting lemma. *)
Lemma dgpr_weight_null_hausdorff_null (B : set RnM) (t : R) : 0 < t -> W B = 0 ->
  (forall x, B x -> (t%:E < upper x)%E) -> HK B = 0.
Proof.
move=> ht hB hd; have [hm _ hbr hf] := dgpr_weight_laws.
have h := @finite_upper_density_hausdorff_bound R RnM k W B t hm hbr hf ht hd.
rewrite hB mule0 in h.
have [hHm _] := @hausdorff_measure_laws R n k.
by apply/eqP; rewrite eq_le h (measure_nonnegative hHm).
Qed.

(** Source for [dgpr_MS_HM]: blueprint thm:MS, (eq:MS:HM):
    H^k(M) ≤ ‖V‖(R^n). By Federer 2.10.19(3) and H^k ≤ S^k,
    t H^k(M) ≤ ‖V‖(R^n) for 0 < t < 1; the conclusion follows as t → 1−.
    Direct formalisation. *)
Theorem dgpr_MS_HM : (HK (dgpr_MS_set W) <= W setT)%E.
Proof.
have [hm _ hbr hf] := dgpr_weight_laws.
have [hHm _] := @hausdorff_measure_laws R n k.
set M := dgpr_MS_set W.
have hb (t : R) : 0 < t -> t < 1 -> (HK M <= (t^-1)%:E * W setT)%E.
  move=> h0 h1.
  apply: le_trans (@finite_upper_density_hausdorff_bound R RnM k W M t hm hbr hf h0 _) _.
  - move=> x [s [hs [hu _]]]; rewrite hu lte_fin; lra.
  - apply: lee_wpmul2l; first by rewrite lee_fin invr_ge0 ltW.
    exact: (measure_mono hm (@subsetT _ M)).
have hW0 : (0 <= W setT)%E := measure_nonnegative hm setT.
have hWf : W setT \is a fin_num by rewrite ge0_fin_numE.
have hM0 : (0 <= HK M)%E := measure_nonnegative hHm M.
have eW : W setT = (fine (W setT))%:E by rewrite fineK.
have hMf : HK M \is a fin_num.
  rewrite ge0_fin_numE //; apply: le_lt_trans (hb (1/2) _ _) _; [lra|lra|].
  by rewrite eW -EFinM ltry.
have eM : HK M = (fine (HK M))%:E by rewrite fineK.
rewrite eM eW lee_fin.
set a := fine (HK M); set w := fine (W setT).
have hw0 : 0 <= w by rewrite -lee_fin -eW.
apply/ler_addgt0Pr => e he.
pose t := (w + 1) / (w + 1 + e).
have hw1 : 0 < w + 1 by lra.
have hwe : 0 < w + 1 + e by lra.
have ht0 : 0 < t by rewrite /t divr_gt0.
have ht1 : t < 1 by rewrite /t ltr_pdivrMr // mul1r; lra.
have := hb t ht0 ht1; rewrite eM eW -EFinM lee_fin => h.
apply: le_trans h _.
have -> : t^-1 * w = w + e * (w / (w + 1)).
  rewrite /t invf_div; field; exact: lt0r_neq0.
rewrite lerD2l; apply: ler_piMr; first exact: ltW.
by rewrite ler_pdivrMr // mul1r; lra.
Qed.

Hypothesis hdens : measure_almost_everywhere W
  [set x | exists t : \bar R, partial_function_graph (@metric_density R RnM k W) x t /\ (1 <= t)%E].

(** Source for [dgpr_MS_set_full]: blueprint thm:MS, “by hypothesis
    and Allard 3.5(1), ‖V‖(R^n ∖ M) = 0”: Θ^k(‖V‖, x) ≥ 1 and
    Θ^k(‖V‖, x) < ∞ for ‖V‖ almost all x. Direct formalisation. *)
Lemma dgpr_MS_set_full : W (~` dgpr_MS_set W) = 0.
Proof.
have [hm _ _ _] := dgpr_weight_laws.
have h2 := allard_3_5_1_a_only_if hV.
have h := measure_almost_everywhere_and hm hdens h2.
apply: (measure_almost_everywhere_mono hm _ h).
move=> x [[t [ht h1]] [[s [hs hgs]] _]].
have hgs' : partial_function_graph (@metric_density R RnM k W) x s%:E := hgs.
have e : t = s%:E := partial_function_single_valued ht hgs'.
exists s; split; last exact: hgs'.
by rewrite e lee_fin in h1.
Qed.

(** Source for [dgpr_MS_borel_part]: Federer 2.2.3, p. 61, applied to
    ‖V‖ and R^n ∖ M: there is a Borel set M' ⊆ M with
    ‖V‖(R^n ∖ M') = 0. This replaces the assertion of blueprint thm:MS
    that M is a Borel set (docs/divergences.md). Supporting lemma. *)
Lemma dgpr_MS_borel_part :
  exists M' : set RnM, [/\ borel_set M', M' `<=` dgpr_MS_set W & W (~` M') = 0].
Proof.
have [hm _ hbr _] := dgpr_weight_laws.
have [B [hB [hBb hWB]]] := borel_regular_cover hbr (~` dgpr_MS_set W).
exists (~` B); split.
- exact: borel_set_complement.
- move=> x hx; apply: contrapT=> hM; exact: hx (hB x hM).
- by rewrite setCK -hWB dgpr_MS_set_full.
Qed.

Section BorelPart.
Variable M' : set RnM.
Hypothesis hM'b : borel_set M'.
Hypothesis hM'M : M' `<=` dgpr_MS_set W.
Hypothesis hM'f : W (~` M') = 0.

(** Source for [dgpr_MS_density]: blueprint thm:MS, the density
    θ(x) = Θ^k(‖V‖, x) for x ∈ M', expressed through the upper density
    Θ^{*k}(‖V‖, x) of Federer 2.10.19, p. 181, which equals Θ^k(‖V‖, x)
    on M' ⊆ M; θ(x) = 0 for x ∈ R^n ∖ M'. Definition. *)
Definition dgpr_MS_density (x : RnM) : R :=
  fine (if `[< M' x >] then upper x else 0%E).

(** Source for [dgpr_MS_density_on]: blueprint thm:MS: for x ∈ M' the
    density Θ^k(‖V‖, x) exists and equals θ(x) ≥ 1. Supporting lemma. *)
Lemma dgpr_MS_density_on x : M' x ->
  1 <= dgpr_MS_density x /\ partial_function_graph (@metric_density R RnM k W) x (dgpr_MS_density x)%:E.
Proof.
move=> hx; have [t [ht hg]] := hM'M hx.
have [hu _] := hg.
by rewrite /dgpr_MS_density asboolT // hu /=.
Qed.

(** Source for [dgpr_MS_density_off]: θ(x) = 0 for x ∈ R^n ∖ M', by
    the definition of [dgpr_MS_density]. Supporting lemma. *)
Lemma dgpr_MS_density_off x : ~ M' x -> dgpr_MS_density x = 0.
Proof. by move=> hx; rewrite /dgpr_MS_density asboolF. Qed.

(** Source for [dgpr_MS_density_ge0]: blueprint mr:hypotheses_main,
    θ ≥ 0. Supporting lemma. *)
Lemma dgpr_MS_density_ge0 x : 0 <= dgpr_MS_density x.
Proof.
case: (pselect (M' x))=> hx.
- have [h _] := dgpr_MS_density_on hx; lra.
- by rewrite dgpr_MS_density_off.
Qed.

(** Source for [dgpr_upper_superlevel_borel]: blueprint thm:MS, “the
    upper and lower densities of ‖V‖ are Borel functions”, for the upper
    density: the set R^n ∩ { x : b < Θ^{*k}(‖V‖, x) } is a Borel set for
    every real number b, because the functions [x ↦ ‖V‖ B(x, r)] are
    upper semicontinuous and Θ^{*k}(‖V‖, x) is the limit superior as
    r → 0+ (Federer 2.10.19, p. 181). Supporting lemma. *)
Lemma dgpr_upper_superlevel_borel (b : R) : borel_set [set x : RnM | (b%:E < upper x)%E].
Proof.
have [hm _ _ _] := dgpr_weight_laws.
change (borel_set [set x : RnM | (b%:E < positive_radius_upper_limit
  (fun r : R => metric_ball_density k W x r))%E]).
rewrite positive_radius_upper_strict_superlevel.
apply: borel_set_countable_union (countableP setT) _=> j _.
apply: borel_set_countable_intersection (countableP setT) _ _.
- by exists 0%N.
- move=> i _; rewrite positive_radius_supremum_strict_level.
  apply: open_borel_set; exact: metric_density_cutoff_superlevel_open hm.
Qed.

(** Source for [dgpr_MS_density_borel]: blueprint thm:MS: θ is a Borel
    function, by [dgpr_upper_superlevel_borel] and Federer 2.3.2(2),
    p. 73. Supporting lemma. *)
Lemma dgpr_MS_density_borel : is_borel_function (fun x : RnM => (dgpr_MS_density x : real_line_metric R)).
Proof.
pose u (x : RnM) : extended_real_line R := if `[< M' x >] then upper x else 0%E.
have hu : is_borel_function u.
  apply: structure_borel_from_strict_superlevels=> b.
  have -> : [set x | (b%:E < u x)%E] =
      (M' `&` [set x | (b%:E < upper x)%E]) `|` (~` M' `&` [set _ | b < 0]).
    apply/seteqP; split=> x; rewrite /u /=.
    - case: (pselect (M' x))=> hx.
      + by rewrite asboolT // => h; left.
      + by rewrite asboolF // lte_fin => h; right.
    - move=> [[hx h]|[hx h]].
      + by rewrite asboolT.
      + by rewrite asboolF // lte_fin.
  apply: borel_setU; first exact: dgpr_borel_setI (dgpr_upper_superlevel_borel b).
  apply: dgpr_borel_setI; first exact: borel_set_complement.
  case: (pselect (b < 0))=> hb.
  - have -> : [set _ : RnM | b < 0] = setT by apply/seteqP; split.
    exact: open_borel_set openT.
  - have -> : [set _ : RnM | b < 0] = set0 by apply/seteqP; split=> x //= h.
    exact: open_borel_set open0.
exact: (borel_function_composition hu (@extended_finite_projection_borel R)).
Qed.

(** Source for [dgpr_MS_density_ae]: blueprint thm:MS, with Federer
    2.10.19(3), p. 181: Θ^k(‖V‖, x) = θ(x) for H^k almost all x ∈ R^n.
    On M' this holds by [dgpr_MS_density_on]. Off M', since
    ‖V‖(R^n ∖ M') = 0, the set of x ∈ R^n ∖ M' with
    Θ^{*k}(‖V‖, x) > 1/(j + 1) is H^k null for every j ∈ N; hence
    Θ^k(‖V‖, x) = 0 = θ(x) for H^k almost all x ∈ R^n ∖ M'.
    Supporting lemma. *)
Lemma dgpr_MS_density_ae :
  measure_almost_equal HK (@metric_density R RnM k W) (real_total_integrand dgpr_MS_density).
Proof.
have [hm _ _ _] := dgpr_weight_laws.
have [hHm _] := @hausdorff_measure_laws R n k.
pose Z := \bigcup_(j in @setT nat) (~` M' `&` [set x | (((j.+1%:R)^-1)%:E < upper x)%E]).
have hZ : HK Z = 0.
  apply: (measure_null_countable_union hHm (countableP setT))=> j _.
  apply: (@dgpr_weight_null_hausdorff_null _ ((j.+1%:R)^-1)).
  - by rewrite invr_gt0 ltr0n.
  - by apply: (measure_null_subset hm _ hM'f)=> x [].
  - by move=> x [].
apply: (measure_null_subset hHm _ hZ)=> x hx.
have hxM : ~ M' x.
  move=> hM; apply: hx; have [_ hg] := dgpr_MS_density_on hM.
  exists (dgpr_MS_density x)%:E; split=> //; exact/real_total_integrand_graph.
have hu0 : upper x != 0%E.
  apply/eqP=> hu; apply: hx; exists 0%E; split.
  - exact/(metric_density_zero_iff_upper_zero _ _ hm).
  - by apply/real_total_integrand_graph; rewrite dgpr_MS_density_off.
have hupos : (0 < upper x)%E.
  by rewrite lt_neqAle eq_sym hu0 (metric_densities_nonnegative k x hm).2.
have [j hj] : exists j : nat, (((j.+1%:R)^-1)%:E < upper x)%E.
  move: hupos; case: (upper x)=> [s||] //= hs.
  - by have [j hj] := dgpr_small_reciprocal (s := s) hs; exists j; rewrite lte_fin.
  - by exists 0%N; exact: ltry.
by exists j.
Qed.

(** Source for [dgpr_MS_weight_representation]: blueprint thm:MS,
    ‖V‖ = (H^k ⌞ M') ⌞ θ, the measure of Federer 2.4.10, p. 85; from
    Allard 3.5(1)(b), ‖V‖ = H^k ⌞ Θ^k(‖V‖, ·), and
    [dgpr_MS_density_ae]. Direct formalisation. *)
Theorem dgpr_MS_weight_representation : W = dgpr_main_measure k M' dgpr_MS_density.
Proof.
have [hHm hHr] := @hausdorff_measure_laws R n k.
have h1 : is_measure_density HK (@metric_density R RnM k W) W.
  rewrite [X in is_measure_density _ _ X](allard_3_5_1_b_weight hV).
  exact: measure_with_density_laws.
have h2 := measure_density_almost_equal hHm h1 dgpr_MS_density_ae.
have hM'm : measure_measurable HK M' := borel_regular_borel_measurable hHm hHr hM'b.
have h3 := supported_density_restricted_reference hHm h2 hM'm
  (fun x hx => proj2 (real_total_integrand_graph dgpr_MS_density x 0%E)
    (congr1 (@EFin R) (dgpr_MS_density_off hx))).
apply: funext=> A.
exact: (measure_density_unique h3 (measure_with_density_laws _ _) A).
Qed.

(** Source for [dgpr_MS_density_summable]: blueprint thm:MS, “θ is
    H^k ⌞ M summable”, for M' in place of M: θ is a nonnegative Borel
    function and ∫ θ d(H^k ⌞ M') = ‖V‖(R^n) < ∞ (Federer 2.4.10, p. 85).
    Direct formalisation. *)
Lemma dgpr_MS_density_summable : summable_real_functions (measure_restrict HK M') dgpr_MS_density.
Proof.
have [hm _ _ hWf] := dgpr_weight_laws.
have [hHm hHr] := @hausdorff_measure_laws R n k.
have hrm := measure_restrict_is_measure hHm M'.
have hmeas : is_measure_measurable_function (measure_restrict HK M')
    (real_total_integrand dgpr_MS_density).
  have h0 := dgpr_borel_restrict_measurable M' dgpr_MS_density_borel.
  exact: (measurable_partial_real_embedding hrm h0).
have hnn : measure_almost_everywhere (measure_restrict HK M')
    (partial_extended_nonnegative_locus (real_total_integrand dgpr_MS_density)).
  have -> : partial_extended_nonnegative_locus (real_total_integrand dgpr_MS_density) = setT.
    apply/seteqP; split=> x // _; exists (dgpr_MS_density x)%:E; split.
    - exact/real_total_integrand_graph.
    - rewrite lee_fin; exact: dgpr_MS_density_ge0.
  exact: measure_almost_everywhere_true hrm.
have [hI hI0] := nonnegative_measurable_function_integral hrm hmeas hnn.
set L := measure_lower_integral _ _ in hI hI0.
have hU := measure_upper_integral_unique (measure_upper_integral_specification _ _) hI.2.1.
have hWs : W setT = dgpr_main_measure k M' dgpr_MS_density setT :=
  congr1 (fun mu => mu setT) dgpr_MS_weight_representation.
have hWL : W setT = L.
  rewrite hWs /dgpr_main_measure (measure_with_density_laws _ _ setT) /measure_subset_upper_integral.
  rewrite -hU; apply: measure_upper_integral_graph_equivalent=> x y.
  rewrite partial_function_zero_extension_graph; split.
  - by move=> [[_ h]|[h _]]; [exact: h|case: h].
  - by move=> h; left.
have hLf : L \is a fin_num by rewrite ge0_fin_numE // -hWL.
by exists (fine L); rewrite fineK.
Qed.

(** Source for [dgpr_MS_rectifiable]: blueprint thm:MS: by Allard 3.5,
    V = Σ_i c_i v(E_i), and A = ⋃_i E_i is countably (H^k, k)
    rectifiable (Federer 3.2.14) with ‖V‖(R^n ∖ A) = 0; by
    [dgpr_weight_null_hausdorff_null], H^k(M' ∖ A) = 0; hence M' is
    countably (H^k, k) rectifiable. Direct formalisation. *)
Lemma dgpr_MS_rectifiable : is_countably_measure_m_rectifiable HK k M'.
Proof.
have [hm _ _ _] := dgpr_weight_laws.
have [hHm _] := @hausdorff_measure_laws R n k.
have [c [E [hc hE _ hWE _]]] := rectifiable_weight_representation hV.
pose U := \bigcup_(i in @setT nat) E i.
have hWU : W (~` U) = 0.
  rewrite hWE /rectifiable_sum_measure.
  have h0 i : [set: nat] i -> (0 <= (c i)%:E * HK (E i `&` ~` U))%E.
    by move=> _; apply: mule_ge0; [rewrite lee_fin ltW|exact: measure_nonnegative hHm _].
  apply/(nonnegative_sum_zero_iff h0).2=> i _.
  have -> : E i `&` ~` U = set0.
    by apply/seteqP; split=> x // [hx hU]; apply: hU; exists i.
  by rewrite measure_empty // mule0.
have hN : HK (M' `\` U) = 0.
  apply: (@dgpr_weight_null_hausdorff_null _ (1 / 2)); first lra.
  - by apply: (measure_null_subset hm _ hWU)=> x [].
  - move=> x [hx _]; have [t [ht [hu _]]] := hM'M hx; rewrite hu lte_fin; lra.
have hEr i : is_countably_measure_m_rectifiable HK k (E i).
  have -> : E i = \bigcup_(j in @setT nat) (E i `&` metric_closed_ball (0 : RnM) j%:R).
    apply/seteqP; split=> [x hx|x [j _ [hx _]]] //.
    exists (Num.bound (mdist (0 : RnM) x))=> //; split=> //.
    rewrite /metric_closed_ball /=; apply: ltW; apply: archi_boundP.
    exact: mdist_ge0.
  apply: (countably_measure_rectifiable_countable_union hHm (countableP _))=> j _.
  exact: ((hE i).2 _ (@euclidean_closed_metric_ball_compact R n (0 : RnM) j%:R)).1.
have hUr : is_countably_measure_m_rectifiable HK k U :=
  countably_measure_rectifiable_countable_union hHm (countableP _) (fun i _ => hEr i).
have hNr := countably_measure_rectifiable_null k hHm hN.
have hcov : M' `<=` \bigcup_(b in @setT bool) (if b then M' `\` U else U).
  move=> x hx; case: (pselect (U x))=> h; [by exists false|by exists true].
apply: (countably_measure_rectifiable_subset hcov).
apply: (countably_measure_rectifiable_countable_union hHm (countableP _))=> b _.
by case: b.
Qed.

(** Source for [dgpr_MS_borel_part_finite]: blueprint thm:MS:
    H^k(M') ≤ H^k(M) ≤ ‖V‖(R^n) < ∞ by (eq:MS:HM). Supporting lemma. *)
Lemma dgpr_MS_borel_part_finite : (HK M' < +oo)%E.
Proof.
have [_ _ _ hWf] := dgpr_weight_laws.
have [hHm _] := @hausdorff_measure_laws R n k.
apply: le_lt_trans (measure_mono hHm hM'M) _.
exact: le_lt_trans dgpr_MS_HM hWf.
Qed.

End BorelPart.
End VarifoldWeight.
