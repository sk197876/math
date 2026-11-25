(** Allard (1972), 3.5, p. 431, and the blueprint proof of al:3.5(1):
    let c_i > 0 and let E_i be locally (H^k, k) rectifiable subsets of R^n,
    and suppose that μ = Σ_i c_i H^k⌞E_i is finite on compact sets. Then the
    k dimensional density Θ^k(μ, x) of Federer 2.10.19, p. 181, equals
    θ(x) = Σ_i c_i 1_{E_i}(x) for H^k almost all x ∈ R^n
    ([rectifiable_sum_density_ae]), and 0 < Θ^k(μ, x) < ∞ for μ almost all x
    ([rectifiable_sum_density_positive_finite]). The proof uses Federer
    3.2.19, p. 256, for the summands and 2.10.19(3)(4), p. 181, for the tails
    of the sum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  cardinality constructive_ereal topology normedtype lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  NormMetric HilbertFormCompactness PartialFunctionUP MeasureUP MeasureBasic MeasureAlmostUP
  MeasureAlmostBasic MeasureRestriction MeasureFiniteClosure MeasureSplit MeasureSum
  FiniteMeasureScaling BorelRegularMeasureUP TopologicalBorel HausdorffMeasure
  HausdorffSphericalComparison SphericalMetricDensityTheorems MetricClosedBalls
  EuclideanClosedBallCompact MetricDensities PositiveRadiusLimits PositiveRadiusLimitBounds
  PositiveRadiusLimitCongruence PositiveRadiusFiniteApproximation
  PositiveRadiusLowerApproximation PositiveRadiusEventualCongruence FinitePositiveRadiusCutoff
  FiniteRadiusMixedLimitComparison ExtendedScaledErrorBound ExtendedRealReciprocalBounds
  ExtendedRealBounds RectifiableDensityTangent NonnegativeSum NonnegativeSumNatPrefix
  NonnegativeSumContinuity NonnegativeSumRestriction.
From Allard Require Import AllardRectifiableVarifolds AllardTangentMeasurability
  AllardRectifiableSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RadiusSums.
Variable R : realType.

(** Source for [nonnegative_sum_nat_prefixE]: Federer 2.1.1, p. 52: the sum of
    a nonnegative sequence over {i : i < N} is the finite sum of its first N
    terms. Supporting lemma. *)
Lemma nonnegative_sum_nat_prefixE (f : nat -> \bar R) N :
  (forall i, (0 <= f i)%E) -> nonnegative_sum [set i | (i < N)%N] f = (\sum_(i < N) f i)%E.
Proof.
move=> hf; elim: N=> [|N ih]; first by rewrite nonnegative_sum_nat_prefix_zero big_ord0.
by rewrite nonnegative_sum_nat_prefix_succ // ih big_ord_recr.
Qed.

(** Source for [finite_radius_upper_sum_comparison]: Federer 2.10.19, p. 181,
    and the finite sums of 3.2.39, p. 276: if f(r) ≤ Σ_j h_j(r) for r > 0 and
    the upper limit of each of the finitely many h_j is at most a_j, then the
    upper limit of f is at most Σ_j a_j. This is the case of
    [finite_radius_mixed_limit_comparison] without lower terms. Supporting
    lemma. *)
Lemma finite_radius_upper_sum_comparison (J : finType) (f : R -> \bar R)
    (h : J -> R -> \bar R) (a : J -> R) :
  (forall j, (positive_radius_upper_limit (h j) <= (a j)%:E)%E) ->
  (forall r : R, 0 < r -> (f r <= \sum_j h j r)%E) ->
  (positive_radius_upper_limit f <= (\sum_j a j)%:E)%E.
Proof.
move=> hU hP.
have hL (i : 'I_0) : (((fun _ : 'I_0 => (0:R)) i)%:E <=
    positive_radius_lower_limit ((fun (_ : 'I_0) (_ : R) => 0%E) i))%E.
  by rewrite (positive_radius_limits_constant (R:=R) 0%E).2.
have hQ (r : R) : 0 < r ->
    (f r + \sum_(i < 0) (fun (_ : 'I_0) (_ : R) => 0%E) i r <= \sum_j h j r)%E.
  by move=> hr; rewrite big_ord0 adde0; exact: hP.
have h0 := @finite_radius_mixed_limit_comparison R 'I_0 J f (fun _ _ => 0%E) h a
  (fun _ => 0) hU hL hQ.
by rewrite big_ord0 subr0 in h0.
Qed.

(** Source for [finite_radius_lower_sum_comparison]: Federer 2.10.19, p. 181:
    if Σ_j h_j(r) ≤ f(r) for r > 0 and a_j does not exceed the lower limit of
    each of the finitely many h_j, then Σ_j a_j does not exceed the lower
    limit of f. Supporting lemma. *)
Lemma finite_radius_lower_sum_comparison (J : finType) (f : R -> \bar R)
    (h : J -> R -> \bar R) (a : J -> R) :
  (forall j, ((a j)%:E <= positive_radius_lower_limit (h j))%E) ->
  (forall r : R, 0 < r -> (\sum_j h j r <= f r)%E) ->
  ((\sum_j a j)%:E <= positive_radius_lower_limit f)%E.
Proof.
move=> hL hP; apply: positive_radius_lower_approximate_bound=> e he.
pose K : R := #|J|%:R + 1.
have hK : 0 < K by rewrite /K ltr_wpDl // ler0n.
have he' : 0 < e / K by rewrite divr_gt0.
have [d [hd hD]] := @finite_common_positive_radius_bound R J
  (fun j r => ((a j - e / K)%:E <= h j r)%E)
  (fun j => @positive_radius_lower_finite_approximation R (h j) (a j) (e / K) (hL j) he').
exists d; split=> // r hr.
apply: le_trans (hP r (andP hr).1).
have hS : (\sum_j (a j - e / K)%:E <= \sum_j h j r)%E.
  by apply: lee_sum=> j _; exact: hD r hr j.
apply: le_trans hS.
rewrite sumEFin lee_fin sumrB sumr_const -mulr_natl.
have hJK : #|J|%:R <= K by rewrite /K; lra.
have h1 : #|J|%:R * (e / K) <= K * (e / K) by rewrite ler_wpM2r // ltW.
have h2 : K * (e / K) = e by rewrite mulrC divfK // gt_eqF.
lra.
Qed.

(** Source for [positive_radius_upper_scale]: Federer 2.10.19, p. 181: if the
    upper limit of g is at most b and c ≥ 0, then the upper limit of [r ↦ c
    g(r)] is at most c b. Supporting lemma. *)
Lemma positive_radius_upper_scale (g : R -> \bar R) (b c : R) :
  0 <= c -> (positive_radius_upper_limit g <= b%:E)%E ->
  (positive_radius_upper_limit (fun r => c%:E * g r) <= (c * b)%:E)%E.
Proof.
move=> hc hg; apply: (@extended_upper_bound_from_scaled_errors R _ (c * b) c hc)=> e he.
have [d [hd hD]] := positive_radius_upper_finite_approximation hg he.
apply: (positive_radius_upper_eventual_bound hd)=> r hr.
rewrite -mulrDr EFinM; apply: lee_wpmul2l; first by rewrite lee_fin.
exact: hD r hr.
Qed.

(** Source for [positive_radius_lower_scale]: Federer 2.10.19, p. 181: if b
    does not exceed the lower limit of g and c ≥ 0, then c b does not exceed
    the lower limit of [r ↦ c g(r)]. Supporting lemma. *)
Lemma positive_radius_lower_scale (g : R -> \bar R) (b c : R) :
  0 <= c -> (b%:E <= positive_radius_lower_limit g)%E ->
  ((c * b)%:E <= positive_radius_lower_limit (fun r => c%:E * g r))%E.
Proof.
move=> hc hg; apply: positive_radius_lower_approximate_bound=> e he.
have he' : 0 < e / (c + 1) by rewrite divr_gt0 // ltr_wpDl.
have [d [hd hD]] := positive_radius_lower_finite_approximation hg he'.
exists d; split=> // r hr.
apply: le_trans (lee_wpmul2l _ (hD r hr)); last by rewrite lee_fin.
rewrite -EFinM lee_fin.
have hc1 : c <= c + 1 by lra.
have h1 : c * (e / (c + 1)) <= (c + 1) * (e / (c + 1)) by rewrite ler_wpM2r // ltW.
have h2 : (c + 1) * (e / (c + 1)) = e by rewrite mulrC divfK // gt_eqF // ltr_wpDl.
rewrite mulrBr; lra.
Qed.

(** Source for [extended_nonnegative_finite]: Federer 2.1.1, p. 51: an
    extended real number between 0 and a real number is real. Supporting
    lemma. *)
Lemma extended_nonnegative_finite (x : \bar R) (y : R) :
  (0 <= x)%E -> (x <= y%:E)%E -> exists p : R, x = p%:E.
Proof. by case: x=> [p _ _|_ //|//]; exists p. Qed.

(** Source for [nonnegative_sum_nat_split]: Federer 2.1.1(2), p. 52: for a
    nonnegative sequence f, Σ_i f(i) = Σ_{i<N} f(i) + Σ_{i≥N} f(i). Supporting
    lemma. *)
Lemma nonnegative_sum_nat_split (f : nat -> \bar R) N :
  (forall i, (0 <= f i)%E) ->
  nonnegative_sum setT f =
    (nonnegative_sum [set i | (i < N)%N] f + nonnegative_sum [set i | (N <= i)%N] f)%E.
Proof.
move=> hf; rewrite (nonnegative_sum_split [set i | (i < N)%N] (fun i _ => hf i)).
have -> : setT `&` [set i | (i < N)%N] = [set i | (i < N)%N] by rewrite setTI.
have -> : setT `\` [set i | (i < N)%N] = [set i | (N <= i)%N].
  apply/seteqP; split=> i /=.
  - by move=> [_ hi]; rewrite leqNgt; apply/negP.
  - by move=> hi; split=> // hlt; move: hi; rewrite leqNgt hlt.
by [].
Qed.

(** Source for [nonnegative_sum_nat_tail_small]: Federer 2.1.1, p. 52: the
    tails Σ_{i≥N} f(i) of a nonnegative series with finite sum become
    arbitrarily small. Supporting lemma. *)
Lemma nonnegative_sum_nat_tail_small (f : nat -> \bar R) (e : R) :
  (forall i, (0 <= f i)%E) -> (nonnegative_sum setT f < +oo)%E -> 0 < e ->
  exists N, (nonnegative_sum [set i | (N <= i)%N] f <= e%:E)%E.
Proof.
move=> hf hs he.
have [s0 hs0] : exists s0 : R, nonnegative_sum setT f = s0%:E.
  move: hs (nonnegative_sum_nonnegative setT f).
  by case: (nonnegative_sum setT f)=> [p _ _|//|//]; exists p.
apply: contrapT=> hno.
have hlt N : (e%:E < nonnegative_sum [set i | (N <= i)%N] f)%E.
  by rewrite ltNge; apply/negP=> hle; apply: hno; exists N.
have hP N : (nonnegative_sum [set i | (i < N)%N] f <= (s0 - e)%:E)%E.
  have hsplit := nonnegative_sum_nat_split N hf; rewrite hs0 in hsplit.
  have hPle : (nonnegative_sum [set i | (i < N)%N] f <= s0%:E)%E.
    rewrite hsplit; apply: leeDl; exact: nonnegative_sum_nonnegative.
  have [p hp] := extended_nonnegative_finite (nonnegative_sum_nonnegative _ _) hPle.
  have hTle : (nonnegative_sum [set i | (N <= i)%N] f <= s0%:E)%E.
    rewrite hsplit; apply: leeDr; exact: nonnegative_sum_nonnegative.
  have [q hq] := extended_nonnegative_finite (nonnegative_sum_nonnegative _ _) hTle.
  have hN := hlt N; rewrite hq lte_fin in hN.
  rewrite hp hq -EFinD in hsplit; have hs1 : s0 = p + q := EFin_inj hsplit.
  rewrite hp lee_fin; lra.
have hsup := @nonnegative_sum_increasing_supremum R nat setT (fun N => [set i | (i < N)%N]) f.
rewrite hsup in hs0; last 3 first.
- by move=> N M hNM i /= hi; exact: leq_trans hi hNM.
- by [].
- by move=> i _; exists i.+1=> /=.
have hbad : (s0%:E <= (s0 - e)%:E)%E.
  rewrite -hs0; apply: extended_real_sup_least=> y [N ->]; exact: hP N.
rewrite lee_fin in hbad; clear -hbad he; lra.
Qed.

(** Source for [extended_null_from_small_multiples]: Federer 2.1.1, p. 51: if
    0 ≤ s, 0 < t and t s ≤ e for every e > 0, then s = 0. Supporting lemma. *)
Lemma extended_null_from_small_multiples (s : \bar R) (t : R) :
  (0 <= s)%E -> 0 < t -> (forall e : R, 0 < e -> (t%:E * s <= e%:E)%E) -> s = 0%E.
Proof.
case: s=> [x hx ht h| _ ht h|//].
- rewrite lee_fin in hx; congr EFin; apply/eqP; rewrite eq_le hx andbT.
  rewrite leNgt; apply/negP=> hx0.
  have hp : 0 < t * x / 2 by rewrite divr_gt0 // mulr_gt0.
  have := h _ hp; rewrite -EFinM lee_fin.
  have : 0 < t * x by rewrite mulr_gt0.
  lra.
- have := h 1 ltr01; by rewrite mulry gtr0_sg // mul1e.
Qed.

(** Source for [extended_null_from_bounded_multiples]: Federer 2.1.1, p. 51:
    if 0 ≤ s, M is real and t s ≤ M for every t > 0, then s = 0. Supporting
    lemma. *)
Lemma extended_null_from_bounded_multiples (s : \bar R) (M : R) :
  (0 <= s)%E -> (forall t : R, 0 < t -> (t%:E * s <= M%:E)%E) -> s = 0%E.
Proof.
case: s=> [x hx h| _ h|//].
- rewrite lee_fin in hx; congr EFin; apply/eqP; rewrite eq_le hx andbT.
  rewrite leNgt; apply/negP=> hx0.
  have ht : 0 < (`|M| + 1) / x by rewrite divr_gt0 // ltr_wpDl.
  have := h _ ht; rewrite -EFinM lee_fin mulrC mulrCA divff ?gt_eqF // mulr1.
  have := ler_norm M; lra.
- have := h 1 ltr01; by rewrite mulry gtr0_sg // mul1e.
Qed.

End RadiusSums.

Section RectifiableDensity.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation RnM := (inner_metric_space hBn).
Local Notation NX := (inner_norm_real_norm hBn).
Local Notation RNM := (real_norm_metric_space NX).
Local Notation HK := (@hausdorff_measure R RnM k).
Local Notation locrect E := (@is_locally_rectifiable_set R n k E).
Local Notation ball j := (metric_closed_ball (0 : RnM) j%:R).

(** Source for [density_eq_le]: Federer 2.1.1, p. 51: equal extended real
    numbers a = b satisfy a ≤ b. Supporting lemma. *)
Let density_eq_le (a b : \bar R) : a = b -> (a <= b)%E.
Proof. by move=> ->. Qed.

(** Source for [restrict_closed_ball_density_local]: Federer 2.10.19, p. 181:
    densities are local. If |x| < j, then B(x, r) ⊆ B(0, j) for 0 < r < j −
    |x|; hence H^k⌞(E ∩ B(0, j)) and H^k⌞E have the same upper and lower
    densities at x. Supporting lemma. *)
Lemma restrict_closed_ball_density_local (E : set RnM) (j : nat) (x : RnM) (y : \bar R) :
  inner_norm hBn x < j%:R ->
  partial_function_graph (@metric_density R RnM k (measure_restrict HK (E `&` ball j))) x y ->
  partial_function_graph (@metric_density R RnM k (measure_restrict HK E)) x y.
Proof.
move=> hx; rewrite !metric_density_graph=> [[hu hl]].
have hd : 0 < j%:R - inner_norm hBn x by rewrite subr_gt0.
have heq (r : R) : 0 < r < j%:R - inner_norm hBn x ->
    metric_ball_density k (measure_restrict HK (E `&` ball j)) x r =
    metric_ball_density k (measure_restrict HK E) x r.
  move=> /andP [hr hrd].
  suff hset : (E `&` ball j) `&` metric_closed_ball x r = E `&` metric_closed_ball x r.
    by rewrite /metric_ball_density /measure_restrict hset.
  apply/seteqP; split=> z.
  - by move=> [[hEz _] hz]; split.
  - move=> [hEz hz]; split=> //; split=> //.
    have ht := metric_triangle (0 : RnM) x z.
    move: hz; rewrite /metric_closed_ball /= => hz.
    rewrite !inner_metric_distanceE !sub0r !inner_normN in ht hz *.
    lra.
have [hl1 hu1] := @positive_radius_limits_eventual_comparison R
  (metric_ball_density k (measure_restrict HK (E `&` ball j)) x)
  (metric_ball_density k (measure_restrict HK E) x) _ hd (fun r hr => density_eq_le (heq r hr)).
have [hl2 hu2] := @positive_radius_limits_eventual_comparison R
  (metric_ball_density k (measure_restrict HK E) x)
  (metric_ball_density k (measure_restrict HK (E `&` ball j)) x) _ hd
  (fun r hr => density_eq_le (esym (heq r hr))).
rewrite /upper_metric_density /lower_metric_density in hu hl *.
split.
- by apply/le_anti; rewrite -hu hu2 hu1.
- by apply/le_anti; rewrite -hl hl2 hl1.
Qed.

(** Source for [locally_rectifiable_density_ae]: Federer 3.2.19, p. 256,
    2.10.19(4), p. 181, and 2.10.6, p. 171: if E is locally (H^k, k)
    rectifiable, then Θ^k(H^k⌞E, x) = 1 for H^k almost all x ∈ E and
    Θ^k(H^k⌞E, x) = 0 for H^k almost all x ∈ R^n ∖ E. The proof applies 3.2.19
    and 2.10.19(4) to E ∩ B(0, j), uses H^k ≤ S^k, and concludes by
    [restrict_closed_ball_density_local]. Supporting lemma. *)
Lemma locally_rectifiable_density_ae (E : set RnM) :
  locrect E ->
  HK [set x | ~ partial_function_graph (@metric_density R RnM k (measure_restrict HK E)) x
    (if `[< E x >] then 1%E else 0%E)] = 0%E.
Proof.
move=> hE; have [hEm hEr] := hE.
have [hm hr] := @hausdorff_measure_laws R n k.
have hBc (j : nat) : compact (ball j) := @euclidean_closed_metric_ball_compact R n (0 : RnM) j%:R.
have hBm (j : nat) : measure_measurable HK (ball j).
  exact: (@borel_regular_borel_measurable R RnM HK hm hr (ball j)
    (closed_borel_set (@metric_closed_ball_closed R RnM (0 : RnM) j%:R))).
have hWm (j : nat) : measure_measurable HK (E `&` ball j) :=
  measure_measurable_intersection hm hEm (hBm j).
pose Z1 (j : nat) := (E `&` ball j) `\` [set w |
  partial_function_graph (@metric_density R RnM k (measure_restrict HK (E `&` ball j))) w 1%E].
pose Z0 (j : nat) := ~` (E `&` ball j) `\` [set w |
  partial_function_graph (@metric_density R RnM k (measure_restrict HK (E `&` ball j))) w 0%E].
have h1 (j : nat) : HK (Z1 j) = 0%E.
  have [h _] := federer_3_2_19 (hEr _ (hBc j)) (hWm j).
  apply: (measure_null_subset hm _ h)=> x [hx hn]; split=> //; move=> [hg _]; exact: hn hg.
have h0 (j : nat) : HK (Z0 j) = 0%E.
  have hs := federer_2_10_19_4 k hm hr (hWm j) (@locally_rectifiable_ball_finite R n k E j hE).
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  have hle := @hausdorff_measure_le_spherical_measure R RnM k (Z0 j).
  apply: le_trans hle _; rewrite /Z0 hs; exact: lexx.
have hZ (j : nat) : HK (Z1 j `|` Z0 j) = 0%E.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  have hc := @measure_binary_cover R RnM HK hm (Z1 j `|` Z0 j) (Z1 j) (Z0 j) (subset_refl _).
  rewrite h1 h0 adde0 in hc; exact: hc.
apply: (measure_null_subset hm _ (measure_null_countable_union hm (countableP [set: nat])
  (fun j _ => hZ j))).
move=> x hbad.
have hxj : inner_norm hBn x < (Num.bound (inner_norm hBn x))%:R.
  exact: (archi_boundP (inner_norm_nonnegative hBn x)).
have hxB : ball (Num.bound (inner_norm hBn x)) x.
  rewrite /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN; exact: ltW.
exists (Num.bound (inner_norm hBn x))=> //.
case: (pselect (E x))=> hEx.
- left; split; first by split.
  move=> hg; apply: hbad; rewrite asboolT //.
  exact: (restrict_closed_ball_density_local hxj hg).
- right; split; first by move=> [hEx' _].
  move=> hg; apply: hbad; rewrite asboolF //.
  exact: (restrict_closed_ball_density_local hxj hg).
Qed.

(** Standing hypotheses for the rest of the section, following Allard 3.5,
    p. 431: c_i > 0, each E_i is locally (H^k, k) rectifiable, and
    μ = Σ_i c_i H^k⌞E_i is finite on compact sets. The last hypothesis is
    [radon_compact_finite] of a Radon measure, and holds for μ = ‖V‖ with
    V ∈ RV_k(R^n). *)
Variables (c : nat -> R) (E : nat -> set RnM).
Hypothesis hc : forall i, 0 < c i.
Hypothesis hE : forall i, locrect (E i).
Hypothesis hfin :
  forall K : set RnM, compact K -> (@rectifiable_sum_measure R n k c E K < +oo)%E.

Local Notation mu := (@rectifiable_sum_measure R n k c E).
Local Notation theta := (@rectifiable_sum_density R n c E).

(** Source for [rectifiable_tail_measure]: Allard 3.5, p. 431: the tail
    Σ_{i≥N} c_i H^k⌞E_i of the measure μ = Σ_i c_i H^k⌞E_i. Definition. *)
Definition rectifiable_tail_measure (N : nat) (A : set RnM) : \bar R :=
  nonnegative_sum [set i | (N <= i)%N] (fun i => ((c i)%:E * HK (E i `&` A))%E).

Local Notation tail N := (rectifiable_tail_measure N).

(** Source for [rectifiable_component_is_measure]: Federer 2.1.2, p. 53: c_i
    H^k⌞E_i is a measure. Supporting lemma. *)
Lemma rectifiable_component_is_measure i :
  is_measure (fun A : set RnM => ((c i)%:E * HK (E i `&` A))%E).
Proof.
have [hm _] := @hausdorff_measure_laws R n k.
exact: (finite_scale_is_measure (measure_restrict_is_measure hm (E i)) (ltW (hc i))).
Qed.

(** Source for [rectifiable_component_measurable]: Federer 2.1.2, p. 53, and
    2.10.1, p. 171: closed sets are c_i H^k⌞E_i measurable, because H^k is a
    Borel regular measure. Supporting lemma. *)
Lemma rectifiable_component_measurable i (S : set RnM) :
  closed S -> measure_measurable (fun A : set RnM => ((c i)%:E * HK (E i `&` A))%E) S.
Proof.
move=> hS T; have [hm hr] := @hausdorff_measure_laws R n k.
have hSm := @borel_regular_borel_measurable R RnM HK hm hr S (closed_borel_set hS).
have h := measure_restrict_measurable (E i) hSm T; rewrite /measure_restrict in h.
rewrite h ge0_muleDr //; exact: (measure_nonnegative hm).
Qed.

(** Source for [rectifiable_tail_is_measure]: Federer 2.1.2, p. 53: the tail
    Σ_{i≥N} c_i H^k⌞E_i is a measure, being a nonnegative sum of measures.
    Supporting lemma. *)
Lemma rectifiable_tail_is_measure N : is_measure (tail N).
Proof.
apply: (@measure_sum_is_measure R RnM nat [set i | (N <= i)%N]
  (fun i A => ((c i)%:E * HK (E i `&` A))%E)); last by [].
move=> i _; exact: rectifiable_component_is_measure.
Qed.

(** Source for [rectifiable_tail_closed_measurable]: Federer 2.1.2, p. 53:
    closed sets are measurable with respect to Σ_{i≥N} c_i H^k⌞E_i, because
    they are measurable with respect to each summand. Supporting lemma. *)
Lemma rectifiable_tail_closed_measurable N (S : set RnM) :
  closed S -> measure_measurable (tail N) S.
Proof.
move=> hS; apply: (@measure_sum_measurable R RnM nat [set i | (N <= i)%N]
  (fun i A => ((c i)%:E * HK (E i `&` A))%E)); last 2 first.
- by [].
- move=> i _; exact: rectifiable_component_measurable.
- move=> i _; exact: rectifiable_component_is_measure.
Qed.

(** Source for [rectifiable_tail_zero]: Allard 3.5, p. 431: the tail with N =
    0 is μ itself. Supporting lemma. *)
Lemma rectifiable_tail_zero : tail 0 = mu.
Proof.
apply: funext=> A; rewrite /rectifiable_tail_measure /rectifiable_sum_measure.
by congr nonnegative_sum; apply/seteqP; split.
Qed.

(** Source for [rectifiable_sum_measure_split]: Federer 2.1.1(2), p. 52: μ(A)
    = Σ_{i<N} c_i H^k(E_i ∩ A) + Σ_{i≥N} c_i H^k(E_i ∩ A). Supporting lemma. *)
Lemma rectifiable_sum_measure_split N (A : set RnM) :
  mu A = (\sum_(i < N) ((c i)%:E * HK (E i `&` A)) + tail N A)%E.
Proof.
have [hm _] := @hausdorff_measure_laws R n k.
have hf i : (0 <= (c i)%:E * HK (E i `&` A))%E.
  by apply: mule_ge0; [rewrite lee_fin ltW|exact: (measure_nonnegative hm)].
rewrite /rectifiable_sum_measure (nonnegative_sum_nat_split N hf).
by rewrite nonnegative_sum_nat_prefixE.
Qed.

(** Source for [rectifiable_ball_density_split]: Federer 2.10.19, p. 181: the
    preceding identity for A = B(x, r), divided by α(k) r^k, splits the ball
    density ratio of μ at x. Supporting lemma. *)
Lemma rectifiable_ball_density_split N (x : RnM) (r : R) :
  0 < r ->
  metric_ball_density k mu x r =
    (\sum_(i < N) ((c i)%:E * metric_ball_density k (measure_restrict HK (E i)) x r) +
      metric_ball_density k (tail N) x r)%E.
Proof.
move=> hr; have [hm _] := @hausdorff_measure_laws R n k.
have hD := @metric_ball_density_denominator_positive R k r hr.
rewrite /metric_ball_density (rectifiable_sum_measure_split N).
rewrite ge0_muleDl; last 2 first.
- by apply: sume_ge0=> i _; apply: mule_ge0; [rewrite lee_fin ltW|exact: (measure_nonnegative hm)].
- exact: (measure_nonnegative (rectifiable_tail_is_measure N)).
congr (_ + _)%E.
rewrite ge0_sume_distrl; last first.
  by move=> i _; apply: mule_ge0; [rewrite lee_fin ltW|exact: (measure_nonnegative hm)].
by apply: eq_bigr=> i _; rewrite /measure_restrict muleA.
Qed.

(** Source for [rectifiable_tail_spherical_bound]: Federer 2.10.19(3), p. 181,
    applied to the tail measure with the open set U(0, j + 1): if G ⊆ B(0, j)
    and t < Θ^{*k}(Σ_{i≥N} c_i H^k⌞E_i, x) for x ∈ G, then t S^k(G) ≤ Σ_{i≥N}
    c_i H^k(E_i ∩ B(0, j + 1)). Supporting lemma. *)
Lemma rectifiable_tail_spherical_bound N (j : nat) (G : set RnM) (t : R) :
  G `<=` ball j ->
  (forall x, G x -> (t%:E < @upper_metric_density R RnM k (tail N) x)%E) ->
  (t%:E * spherical_measure k G <= tail N (ball j.+1))%E.
Proof.
move=> hGB hG.
pose V := [set y : RnM | mdist (0 : RnM) y < j.+1%:R].
have hVo : open V := @metric_open_ball_open R RnM (0 : RnM) j.+1%:R.
have hGV : G `<=` V.
  move=> y /hGB; rewrite /metric_closed_ball /V /= => hy.
  apply: le_lt_trans hy _; rewrite ltr_nat; exact: ltnSn.
apply: le_trans (federer_2_10_19_3 (rectifiable_tail_is_measure N)
  (rectifiable_tail_closed_measurable N) hVo hGV hG) _.
apply: (measure_mono (rectifiable_tail_is_measure N))=> y; rewrite /V /metric_closed_ball /=.
exact: ltW.
Qed.

(** Source for [rectifiable_tail_upper_density_null]: Federer 2.10.19(3), p.
    181, and 2.10.6, p. 171: if t > 0, then the points x ∈ B(0, j) with t <
    Θ^{*k}(Σ_{i≥N} c_i H^k⌞E_i, x) for every N form an H^k null set, because
    μ(B(0, j + 1)) < ∞ makes the tails at B(0, j + 1) arbitrarily small.
    Supporting lemma. *)
Lemma rectifiable_tail_upper_density_null (j : nat) (t : R) :
  0 < t ->
  HK (ball j `&` [set x | forall N, (t%:E < @upper_metric_density R RnM k (tail N) x)%E]) = 0%E.
Proof.
move=> ht; have [hm _] := @hausdorff_measure_laws R n k.
set H := ball j `&` _.
have hf i : (0 <= (c i)%:E * HK (E i `&` ball j.+1))%E.
  by apply: mule_ge0; [rewrite lee_fin ltW|exact: (measure_nonnegative hm)].
have hK := hfin (@euclidean_closed_metric_ball_compact R n (0 : RnM) j.+1%:R).
have hS : spherical_measure k H = 0%E.
  apply: (extended_null_from_small_multiples _ ht).
  - exact: (measure_nonnegative (@spherical_measure_is_measure R RnM k)).
  move=> e he.
  have [N hN] := nonnegative_sum_nat_tail_small hf hK he.
  apply: le_trans hN.
  apply: (rectifiable_tail_spherical_bound (j:=j)); first by move=> x [].
  by move=> x [_ hx]; exact: hx N.
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
have hle := @hausdorff_measure_le_spherical_measure R RnM k H.
by rewrite hS in hle.
Qed.

(** Source for [rectifiable_infinite_upper_density_null]: Federer 2.10.19(3),
    p. 181, and 2.10.6, p. 171: the points x ∈ B(0, j) with Θ^{*k}(μ, x) = ∞
    form an H^k null set, because μ(B(0, j + 1)) < ∞. Supporting lemma. *)
Lemma rectifiable_infinite_upper_density_null (j : nat) :
  HK (ball j `&` [set x | forall t : R, (t%:E < @upper_metric_density R RnM k mu x)%E]) = 0%E.
Proof.
have [hm _] := @hausdorff_measure_laws R n k.
set H := ball j `&` _.
have hK := hfin (@euclidean_closed_metric_ball_compact R n (0 : RnM) j.+1%:R).
have [M hM] : exists M : R, mu (ball j.+1) = M%:E.
  move: hK (measure_nonnegative (rectifiable_tail_is_measure 0) (ball j.+1)).
  rewrite rectifiable_tail_zero.
  by case: (mu (ball j.+1))=> [p _ _|//|//]; exists p.
have hS : spherical_measure k H = 0%E.
  apply: (@extended_null_from_bounded_multiples R _ M).
  - exact: (measure_nonnegative (@spherical_measure_is_measure R RnM k)).
  move=> t ht; rewrite -hM -rectifiable_tail_zero.
  apply: (rectifiable_tail_spherical_bound (j:=j)); first by move=> x [].
  by move=> x [_ hx]; rewrite rectifiable_tail_zero; exact: hx t.
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
have hle := @hausdorff_measure_le_spherical_measure R RnM k H.
by rewrite hS in hle.
Qed.

(** Source for [rectifiable_density_prefix_le]: Federer 2.1.1, p. 52: Σ_{i<N}
    c_i 1_{E_i}(x) ≤ θ(x). Supporting lemma. *)
Lemma rectifiable_density_prefix_le (x : RnM) N :
  ((\sum_(i < N) (if `[< E i x >] then c i else 0))%:E <= theta x)%E.
Proof.
have hf i : (0 <= (if `[< E i x >] then (c i)%:E else 0%E))%E.
  by case: ifP=> _ //; rewrite lee_fin ltW.
apply: le_trans (nonnegative_sum_subset _ (subsetT [set i | (i < N)%N])).
rewrite nonnegative_sum_nat_prefixE // -sumEFin.
by apply: lee_sum=> i _; case: ifP.
Qed.

(** Source for [rectifiable_sum_upper_density_bound]: blueprint proof of
    al:3.5(1): suppose Θ^k(H^k⌞E_i, x) = 1_{E_i}(x) for every i, and for every
    m there is N with Θ^{*k}(Σ_{i≥N} c_i H^k⌞E_i, x) ≤ 1/(m + 1). Then
    Θ^{*k}(μ, x) ≤ Σ_{i<N} c_i 1_{E_i}(x) + 1/(m + 1) by finite subadditivity
    of upper limits; hence Θ^{*k}(μ, x) ≤ θ(x). Supporting lemma. *)
Lemma rectifiable_sum_upper_density_bound (x : RnM) :
  (forall i, partial_function_graph (@metric_density R RnM k (measure_restrict HK (E i))) x
    (if `[< E i x >] then 1%E else 0%E)) ->
  (forall m : nat, exists N,
    (@upper_metric_density R RnM k (tail N) x <= ((m.+1)%:R^-1)%:E)%E) ->
  (@upper_metric_density R RnM k mu x <= theta x)%E.
Proof.
move=> hx ht.
have hθ0 : (0 <= theta x)%E by exact: nonnegative_sum_nonnegative.
case hθ: (theta x)=> [θ0| |]; last 2 first.
- exact: leey.
- by rewrite hθ in hθ0.
apply: extended_real_reciprocal_upper_bound=> m.
have [N hN] := ht m.
pose a (j : 'I_N.+1) : R :=
  if (j < N)%N then (if `[< E j x >] then c j else 0) else (m.+1)%:R^-1.
pose h (j : 'I_N.+1) (r : R) : \bar R :=
  if (j < N)%N then ((c j)%:E * metric_ball_density k (measure_restrict HK (E j)) x r)%E
  else metric_ball_density k (tail N) x r.
apply: le_trans (@finite_radius_upper_sum_comparison R _ (metric_ball_density k mu x) h a _ _) _.
- move=> j; rewrite /h /a; case: ifP=> _ /=; last exact: hN.
  have [hu _] := hx j; rewrite /upper_metric_density in hu.
  case: (pselect (E j x))=> hEj.
  - rewrite (asboolT hEj) in hu *.
    have hs := @positive_radius_upper_scale R
      (metric_ball_density k (measure_restrict HK (E j)) x) 1 (c j) (ltW (hc j)).
    rewrite hu mulr1 in hs; exact: hs (lexx _).
  - rewrite (asboolF hEj) in hu *.
    have hs := @positive_radius_upper_scale R
      (metric_ball_density k (measure_restrict HK (E j)) x) 0 (c j) (ltW (hc j)).
    rewrite hu mulr0 in hs; exact: hs (lexx _).
- move=> r hr; rewrite (rectifiable_ball_density_split N x hr) big_ord_recr /= /h ltnn.
  apply: leeD; last exact: lexx.
  apply: lee_sum=> j _.
  have -> : (widen_ord (leqnSn N) j < N)%N = true by exact: ltn_ord j.
  exact: lexx.
- rewrite big_ord_recr /= /a ltnn lee_fin.
  have hP := rectifiable_density_prefix_le x N; rewrite hθ lee_fin in hP.
  apply: lerD; last exact: lexx.
  apply: le_trans hP; apply: ler_sum=> j _.
  have -> : (widen_ord (leqnSn N) j < N)%N = true by exact: ltn_ord j.
  exact: lexx.
Qed.

(** Source for [rectifiable_sum_lower_density_bound]: blueprint proof of
    al:3.5(1): if Θ^k(H^k⌞E_i, x) = 1_{E_i}(x) for every i, then Σ_{i<N} c_i
    1_{E_i}(x) ≤ Θ_*^k(μ, x) for every N, by superadditivity of lower limits;
    hence θ(x) ≤ Θ_*^k(μ, x). Supporting lemma. *)
Lemma rectifiable_sum_lower_density_bound (x : RnM) :
  (forall i, partial_function_graph (@metric_density R RnM k (measure_restrict HK (E i))) x
    (if `[< E i x >] then 1%E else 0%E)) ->
  (theta x <= @lower_metric_density R RnM k mu x)%E.
Proof.
move=> hx; have [hm _] := @hausdorff_measure_laws R n k.
have hf i : (0 <= (if `[< E i x >] then (c i)%:E else 0%E))%E.
  by case: ifP=> _ //; rewrite lee_fin ltW.
rewrite /rectifiable_sum_density (@nonnegative_sum_increasing_supremum R nat setT
  (fun N => [set i | (i < N)%N])); last 3 first.
- by move=> N M hNM i /= hi; exact: leq_trans hi hNM.
- by [].
- by move=> i _; exists i.+1=> /=.
apply: extended_real_sup_least=> y [N ->].
have -> : nonnegative_sum [set i | (i < N)%N] (fun i => if `[< E i x >] then (c i)%:E else 0%E) =
    (\sum_(i < N) (if `[< E i x >] then c i else 0))%:E.
  rewrite nonnegative_sum_nat_prefixE // -sumEFin.
  by apply: eq_bigr=> i _; case: ifP.
apply: (@finite_radius_lower_sum_comparison R _ (metric_ball_density k mu x)
  (fun (i : 'I_N) r => ((c i)%:E * metric_ball_density k (measure_restrict HK (E i)) x r)%E)).
- move=> i; have [_ hl] := hx i; rewrite /lower_metric_density in hl.
  case: (pselect (E i x))=> hEi.
  - rewrite (asboolT hEi) in hl *.
    have hs := @positive_radius_lower_scale R
      (metric_ball_density k (measure_restrict HK (E i)) x) 1 (c i) (ltW (hc i)).
    rewrite hl mulr1 in hs; exact: hs (lexx _).
  - rewrite (asboolF hEi) in hl *.
    have hs := @positive_radius_lower_scale R
      (metric_ball_density k (measure_restrict HK (E i)) x) 0 (c i) (ltW (hc i)).
    rewrite hl mulr0 in hs; exact: hs (lexx _).
- move=> r hr; rewrite (rectifiable_ball_density_split N x hr).
  apply: leeDl; apply: mule_ge0.
  + exact: (measure_nonnegative (rectifiable_tail_is_measure N)).
  + by rewrite inve_ge0 lee_fin ltW // metric_ball_density_denominator_positive.
Qed.

(** Source for [rectifiable_sum_density_ae]: Allard 3.5, p. 431, and the
    blueprint proof of al:3.5(1): Θ^k(μ, x) = θ(x) for H^k almost all x ∈ R^n,
    where μ = Σ_i c_i H^k⌞E_i and θ = Σ_i c_i 1_{E_i}. The exceptional set is
    the union of the exceptional sets of [locally_rectifiable_density_ae] and
    of [rectifiable_tail_upper_density_null]. Direct formalisation. *)
Theorem rectifiable_sum_density_ae :
  measure_almost_everywhere_on HK setT
    [set x | partial_function_graph (@metric_density R RNM k mu) x (theta x)].
Proof.
have [hm _] := @hausdorff_measure_laws R n k.
pose Z (i : nat) := [set x | ~ partial_function_graph
  (@metric_density R RnM k (measure_restrict HK (E i))) x (if `[< E i x >] then 1%E else 0%E)].
pose H (p : nat * nat) := ball p.1 `&` [set x | forall N,
  ((p.2.+1%:R^-1)%:E < @upper_metric_density R RnM k (tail N) x)%E].
have hZ : HK (\bigcup_(i in setT) Z i) = 0%E.
  apply: (measure_null_countable_union hm (countableP [set: nat]))=> i _.
  exact: (locally_rectifiable_density_ae (hE i)).
have hH : HK (\bigcup_(p in setT) H p) = 0%E.
  apply: (measure_null_countable_union hm (countableP [set: nat * nat]))=> p _.
  by apply: rectifiable_tail_upper_density_null; rewrite invr_gt0 ltr0n.
have hU : HK ((\bigcup_(i in setT) Z i) `|` (\bigcup_(p in setT) H p)) = 0%E.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  have hcov := @measure_binary_cover R RnM HK hm _ (\bigcup_(i in setT) Z i)
    (\bigcup_(p in setT) H p) (subset_refl _).
  rewrite hZ hH adde0 in hcov; exact: hcov.
rewrite /measure_almost_everywhere_on; apply: (measure_null_subset hm _ hU).
move=> x [_ hbad]; apply: contrapT=> hgood.
have hx i : partial_function_graph (@metric_density R RnM k (measure_restrict HK (E i))) x
    (if `[< E i x >] then 1%E else 0%E).
  by apply: contrapT=> hn; apply: hgood; left; exists i.
have [j hj] := @closed_ball_cover R n x.
have ht (m : nat) : exists N,
    (@upper_metric_density R RnM k (tail N) x <= ((m.+1)%:R^-1)%:E)%E.
  apply: contrapT=> hno; apply: hgood; right; exists (j, m)=> //; split=> // N.
  by rewrite ltNge; apply/negP=> hle; apply: hno; exists N.
apply: hbad; change (partial_function_graph (@metric_density R RnM k mu) x (theta x)).
have hu := rectifiable_sum_upper_density_bound hx ht.
have hl := rectifiable_sum_lower_density_bound hx.
have ho := @metric_densities_ordered R RnM k mu x.
rewrite metric_density_graph; split; apply/le_anti/andP; split=> //.
- exact: le_trans hl ho.
- exact: le_trans ho hu.
Qed.

(** Source for [rectifiable_sum_density_positive_finite]: Allard 3.5, p. 431:
    0 < Θ^k(μ, x) < ∞ for μ almost all x. Since μ(Z) = Σ_i c_i H^k(E_i ∩ Z),
    it suffices that H^k almost all x ∈ E_i satisfy the assertion; there
    Θ^k(μ, x) = θ(x) ≥ c_i > 0 by [rectifiable_sum_density_ae], and θ(x) < ∞
    by [rectifiable_infinite_upper_density_null]. Direct formalisation. *)
Theorem rectifiable_sum_density_positive_finite :
  measure_almost_everywhere mu
    [set x | exists t : R,
      0 < t /\ partial_function_graph (@metric_density R RNM k mu) x t%:E].
Proof.
have [hm _] := @hausdorff_measure_laws R n k.
set P := [set x | exists t : R, _].
pose G (j : nat) := ball j `&`
  [set x | forall t : R, (t%:E < @upper_metric_density R RnM k mu x)%E].
have hA := rectifiable_sum_density_ae.
rewrite /measure_almost_everywhere_on in hA.
have hG : HK (\bigcup_(j in setT) G j) = 0%E.
  apply: (measure_null_countable_union hm (countableP [set: nat]))=> j _.
  exact: rectifiable_infinite_upper_density_null.
set Good := [set x | partial_function_graph (@metric_density R RNM k mu) x (theta x)].
have hU : HK ((setT `\` Good) `|` (\bigcup_(j in setT) G j)) = 0%E.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  have hcov := @measure_binary_cover R RnM HK hm _ (setT `\` Good)
    (\bigcup_(j in setT) G j) (subset_refl _).
  rewrite hA hG adde0 in hcov; exact: hcov.
rewrite /measure_almost_everywhere /rectifiable_sum_measure.
apply: nonnegative_sum_zero=> i _.
suff -> : HK (E i `&` ~` P) = 0%E by rewrite mule0.
apply: (measure_null_subset hm _ hU)=> x [hEi hnP].
case: (pselect (Good x))=> hgx; last by left.
right; have [j hj] := @closed_ball_cover R n x; exists j=> //; split=> // t.
have hθ : ((c i)%:E <= theta x)%E.
  have h := @nonnegative_sum_term R nat setT
    (fun l => if `[< E l x >] then (c l)%:E else 0%E) i I.
  by rewrite /= (asboolT hEi) in h.
have [hu _] := (metric_density_graph _ _ _ _).1 hgx.
change (@upper_metric_density R RnM k mu x = theta x) in hu.
rewrite hu.
case hθx: (theta x) hθ=> [θ0| |] hθ.
- exfalso; apply: hnP; exists θ0; split.
  + by rewrite lee_fin in hθ; exact: lt_le_trans (hc i) hθ.
  + by rewrite -hθx.
- exact: ltey.
- by rewrite leeNy_eq in hθ.
Qed.

End RectifiableDensity.
