(** Allard (1972), 3.5(1), p. 432, specialised to M = U = R^n; blueprint
    proof of al:3.5(1) through new:density_tangent. For V ∈ RV_k(R^n):
    Θ^k(‖V‖, x) ∈ (0, ∞) and Tan^k(‖V‖, x) ∈ G(n, k) for ‖V‖ almost all x
    ([allard_3_5_1_a_only_if]); ‖V‖ = H^k⌞Θ^k(‖V‖, ·) in the sense of
    Federer 2.4.10, p. 85 ([allard_3_5_1_b_weight]); [x ↦ Tan^k(‖V‖, x)] is
    ‖V‖ measurable ([allard_3_5_1_b_measurable]); and
    V(f) = ∫ f(x, Tan^k(‖V‖, x)) d‖V‖ x for every real valued Borel function
    f on G_k(R^n) ([allard_3_5_1_b_integral]). The weight formula is proved
    for μ = Σ_i c_i H^k⌞E_i first with the density θ = Σ_i c_i 1_{E_i}
    ([rectifiable_sum_measure_with_density]) and then with Θ^k(μ, ·), which
    equals θ at H^k almost all points (AllardRectifiableDensity.v). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology normedtype lra cardinality.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  InnerNorm InnerMetric NormMetric HilbertFormCompactness LinearBasis FiniteCoordinates Hom HomInner
  GrassmannSubspaces PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition
  PartialFunctionPrecomposition MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureRestriction RadonMeasureUP BorelRegularMeasureUP TopologicalBorel BorelFunctionUP
  BorelFunctionBasic HausdorffMeasure HausdorffClosedCoverAgreement MetricClosedBalls
  EuclideanClosedBallCompact MeasurableFunctionUP MeasureApproximateTangentUP RectifiableTangentPlaneUP
  RectifiableSetUP MeasureFiniteClosure MeasureCountableClosure MeasureNullModification
  MeasurePushforward MeasureSplit NonnegativeSum BorelProductMaps BorelGraphs InnerSpaceCountableBase
  CompactMetricSeparability CountableOpenBaseUP CountableLocalFiniteMetricRadon MeasureIntegralUP
  MeasureIntegralAlmostEquality SummableRealFunctionUP MeasureStepIntegralIdentification
  PushforwardIntegral BVCurveMeasurable OrthonormalFamilies CoordinateProjection
  MeasurableGraphEquivalence ExtendedRealOrderTopology RealMetricBackground
  LusinBorelVersion RadonBorelRegularity CountablyMeasurableUP NonnegativeSumSupport
  MeasureDensityUP MeasureDensity MeasureDensityTransfer DensityCharacteristicIntegral
  DensityMeasurableAlmostCover MeasureCountableNonnegativeSum MeasureExtendedCharacteristicIntegral
  CharacteristicFunctionUP PartialNumericalSum NumericalSum MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence PartialZeroExtension PartialZeroExtensionLaws PartialExtendedOrderLoci
  MeasureSubsetIntegral MeasureIntegralBounds MetricDensities.
From Allard Require Import AllardOrthogonalProjectors AllardGrassmann AllardGrassmannSubspaces
  AllardVarifolds AllardRectifiableVarifolds AllardTangentMeasurability
  AllardSetVarifold AllardRectifiableSum AllardRectifiableIntegral AllardRectifiableTangent
  AllardRectifiableDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section WeightDensity.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation RnM := (inner_metric_space hBn).
Local Notation NX := (inner_norm_real_norm hBn).
Local Notation RNM := (real_norm_metric_space NX).
Local Notation HK := (@hausdorff_measure R RnM k).
Local Notation locrect E := (@is_locally_rectifiable_set R n k E).

Variables (c : nat -> R) (E : nat -> set RnM).
Hypothesis hc : forall i, 0 < c i.
Hypothesis hE : forall i, locrect (E i).
Local Notation mu := (@rectifiable_sum_measure R n k c E).
Local Notation theta := (@rectifiable_sum_density R n c E).

(** Source for [rectifiable_sum_density_function]: blueprint proof of
    al:3.5(1): θ = Σ_i c_i 1_{E_i} as a total extended real valued function
    on R^n. Definition. *)
Definition rectifiable_sum_density_function : partial_function RnM (extended_real_line R) :=
  partial_function_total (fun x => (theta x : extended_real_line R)).
Local Notation thf := rectifiable_sum_density_function.

(** Source for [rectifiable_indicator]: Federer 2.2.14, p. 70: the
    characteristic function of A ⊆ R^n. Definition. *)
Definition rectifiable_indicator (A : set RnM) (x : RnM) : R := if `[< A x >] then 1 else 0.

(** Source for [rectifiable_indicator_characteristic]: Federer 2.2.14,
    p. 70: [rectifiable_indicator A] is the characteristic function of A.
    Supporting lemma. *)
Lemma rectifiable_indicator_characteristic A : is_characteristic_function A (rectifiable_indicator A).
Proof.
by constructor=> x hx; rewrite /rectifiable_indicator; [rewrite asboolT|rewrite asboolF].
Qed.

(** Source for [rectifiable_component_function]: blueprint proof of
    al:3.5(1): the summand c_i 1_{E_i ∩ B} of θ 1_B. Definition. *)
Definition rectifiable_component_function (B : set RnM) (i : nat) :
    partial_function RnM (extended_real_line R) :=
  partial_function_total (fun x => ((c i)%:E * (rectifiable_indicator (E i `&` B) x)%:E : extended_real_line R)%E).

(** Source for [rectifiable_component_value]: c_i 1_{E_i ∩ B}(x) equals
    c_i 1_{E_i}(x) for x ∈ B and 0 otherwise. Supporting lemma. *)
Lemma rectifiable_component_value B i x :
  ((c i)%:E * (rectifiable_indicator (E i `&` B) x)%:E)%E = if `[< B x >] then (if `[< E i x >] then (c i)%:E else 0%E) else 0%E.
Proof.
rewrite /rectifiable_indicator.
case: (pselect (B x))=> hB; case: (pselect (E i x))=> hEx.
- have -> : `[< (E i `&` B) x >] = true by apply/asboolP.
  by rewrite (asboolT hB) (asboolT hEx) mule1.
- have -> : `[< (E i `&` B) x >] = false by apply/asboolP=> -[].
  by rewrite (asboolT hB) (asboolF hEx) mule0.
- have -> : `[< (E i `&` B) x >] = false by apply/asboolP=> -[].
  by rewrite (asboolF hB) mule0.
- have -> : `[< (E i `&` B) x >] = false by apply/asboolP=> -[].
  by rewrite (asboolF hB) mule0.
Qed.

(** Source for [rectifiable_component_nonnegative]: c_i 1_{E_i ∩ B} ≥ 0,
    since c_i > 0. Supporting lemma. *)
Lemma rectifiable_component_nonnegative B i x : (0 <= (c i)%:E * (rectifiable_indicator (E i `&` B) x)%:E)%E.
Proof.
apply: mule_ge0; first by rewrite lee_fin; exact: ltW (hc i).
by rewrite /rectifiable_indicator; case: asboolP=> _; rewrite lee_fin.
Qed.

(** Source for [rectifiable_component_sum_graph]: Federer 2.1.1(3)(4),
    p. 52, and 2.4.8, p. 84: the pointwise sum Σ_i c_i 1_{E_i ∩ B} is θ 1_B.
    Supporting lemma. *)
Lemma rectifiable_component_sum_graph B x y :
  partial_function_graph (partial_function_numerical_sum [set: nat] (rectifiable_component_function B)) x y <->
  partial_function_graph (partial_function_zero_extension (0 : extended_real_line R) B thf) x y.
Proof.
rewrite partial_function_numerical_sum_graph partial_function_zero_extension_graph.
have hs : numerical_sum [set: nat] (fun i => ((c i)%:E * (rectifiable_indicator (E i `&` B) x)%:E)%E) =
    Some (if `[< B x >] then theta x else 0%E).
  rewrite numerical_sum_nonnegative; last by move=> i _; exact: rectifiable_component_nonnegative.
  congr Some; case: (pselect (B x))=> hB.
  - rewrite asboolT // /rectifiable_sum_density; apply: nonnegative_sum_ext=> i _.
    by rewrite rectifiable_component_value asboolT.
  - rewrite asboolF //; apply: nonnegative_sum_zero=> i _.
    by rewrite rectifiable_component_value asboolF.
split.
- move=> [u [hu hsum]].
  have eu : u = (fun i => ((c i)%:E * (rectifiable_indicator (E i `&` B) x)%:E)%E).
    by apply: funext=> i; rewrite -(hu i I).
  rewrite eu hs in hsum; case: hsum=> <-.
  case: (pselect (B x))=> hB; [left; rewrite asboolT|right; rewrite asboolF] => //.
- move=> h; exists (fun i => ((c i)%:E * (rectifiable_indicator (E i `&` B) x)%:E)%E); split=> //.
  rewrite hs; case: h=> [[hB hy]|[hB ->]].
  + by rewrite asboolT // hy.
  + by rewrite asboolF.
Qed.

(** Source for [rectifiable_density_subset_integral]: Federer 2.4.8, p. 84
    (monotone convergence for countable sums), 2.4.10, p. 85, and 2.2.14,
    p. 70: ∫_B θ dH^k = Σ_i c_i H^k(E_i ∩ B) = μ(B) for every H^k measurable
    set B. Supporting lemma. *)
Lemma rectifiable_density_subset_integral B : measure_measurable HK B ->
  is_measure_integral HK (partial_function_zero_extension (0 : extended_real_line R) B thf) (mu B).
Proof.
move=> hB; have [hHm _] := @hausdorff_measure_laws R n k.
have hi i : is_measure_integral HK (rectifiable_component_function B i) ((c i)%:E * HK (E i `&` B))%E.
  apply: (@measure_nonnegative_extended_characteristic_integral R _ HK hHm (E i `&` B)
    (rectifiable_indicator (E i `&` B)) (c i)%:E (rectifiable_indicator_characteristic _)).
  - exact: (@measure_measurable_intersection R _ HK hHm (E i) B (hE i).1 hB).
  - by rewrite lee_fin; exact: ltW (hc i).
have hsum := @measure_countable_nonnegative_sum_integral R RnM nat HK hHm [set: nat]
  (rectifiable_component_function B) (countableP _) (fun i _ => (hi i).1)
  (fun i _ x y hy => ltac:(rewrite -hy; exact: rectifiable_component_nonnegative)).
have e : nonnegative_sum [set: nat] (fun i => measure_lower_integral HK (rectifiable_component_function B i)) = mu B.
  rewrite /rectifiable_sum_measure; apply: nonnegative_sum_ext=> i _.
  exact: measure_lower_integral_unique (measure_lower_integral_specification _ _) (hi i).2.2.
rewrite e in hsum.
exact: measure_integral_graph_equivalent (rectifiable_component_sum_graph B) hsum.
Qed.

(** Source for [rectifiable_density_measurable]: Federer 2.4.8, p. 84: θ is
    H^k measurable. Supporting lemma. *)
Lemma rectifiable_density_measurable : is_measure_measurable_function HK thf.
Proof.
have [hHm hHr] := @hausdorff_measure_laws R n k.
have hT : measure_measurable HK [set: RnM].
  move=> T; rewrite setIT.
  have -> : T `\` [set: RnM] = set0 by apply/seteqP; split=> x // [_ []].
  by rewrite measure_empty // adde0.
have h := (rectifiable_density_subset_integral hT).1.
apply: (measurable_function_graph_equivalent _ h)=> x y.
exact: partial_zero_extension_whole_graph.
Qed.

(** Source for [rectifiable_density_nonnegative]: θ ≥ 0 everywhere.
    Supporting lemma. *)
Lemma rectifiable_density_nonnegative :
  measure_almost_everywhere HK (partial_extended_nonnegative_locus thf).
Proof.
have [hHm _] := @hausdorff_measure_laws R n k.
rewrite /measure_almost_everywhere.
have -> : ~` partial_extended_nonnegative_locus thf = set0.
  apply/seteqP; split=> // x hx; exfalso; apply: hx.
  exists (theta x); split=> //; exact: nonnegative_sum_nonnegative.
exact: measure_empty.
Qed.

(** Standing hypotheses for the rest of the section: μ is a Radon measure,
    as it is when μ = ‖V‖ for V ∈ RV_k(R^n) (Allard 3.1). *)
Hypotheses (hm : is_measure mu) (hr : is_radon_measure mu).

(** Source for [rectifiable_sum_measure_with_density]: blueprint proof of
    al:3.5(1), with Federer 2.4.10, p. 85: μ = H^k⌞θ on all subsets of
    R^n. The two measures agree on H^k measurable sets; for an arbitrary
    set A, Borel regularity of μ (Federer 2.2.5, p. 61) gives
    (H^k⌞θ)(A) ≤ μ(A), and H^k measurable covers of A with almost the same
    H^k⌞θ measure give μ(A) ≤ (H^k⌞θ)(A). Direct formalisation. *)
Lemma rectifiable_sum_measure_with_density :
  mu = measure_with_density HK thf.
Proof.
have [hHm hHr] := @hausdorff_measure_laws R n k.
pose nu := measure_with_density HK thf.
have hn : is_measure_density HK thf nu := measure_with_density_laws HK thf.
have hp := rectifiable_density_nonnegative.
have hf := rectifiable_density_measurable.
have hnm : is_measure nu := measure_with_density_is_measure hHm hp.
have heq B : measure_measurable HK B -> nu B = mu B.
  move=> hB.
  have h1 := @measurable_density_subset_integral R RnM HK nu hHm thf B hn hp hf hB.
  exact: measure_integral_unique h1 (rectifiable_density_subset_integral hB).
have hb := radon_borel_regular hm hr.
apply: funext=> A; apply/eqP; rewrite eq_le; apply/andP; split.
- case: (ltP (nu A) +oo)%E=> hA; last exact: le_trans (leey _) hA.
  apply/lee_addgt0Pr=> e he.
  have [C [hC [hAC hCe]]] := @density_measurable_almost_cover R RnM HK nu thf A e hHm hn hf hp hA he.
  apply: (le_trans (@measure_mono R _ mu hm A C hAC)); rewrite -(heq C hC); exact: ltW.
- have [B [hAB [hB hAeq]]] := borel_regular_cover hb A.
  rewrite hAeq -(heq B (borel_regular_borel_measurable hHm hHr hB)).
  exact: (@measure_mono R _ nu hnm A B hAB).
Qed.

(** Source for [rectifiable_sum_measure_metric_density]: Allard 3.5(1)(b),
    p. 432, and blueprint new:density_tangent(a): μ = H^k⌞Θ^k(μ, ·), since
    Θ^k(μ, x) = θ(x) for H^k almost all x (Federer 2.4.10, p. 85, null
    modifications of the density). Direct formalisation. *)
Lemma rectifiable_sum_measure_metric_density :
  mu = measure_with_density HK (@metric_density R RNM k mu).
Proof.
have [hHm _] := @hausdorff_measure_laws R n k.
have hfin (K : set RnM) (hK : compact K) : (mu K < +oo)%E := radon_compact_finite hr hK.
have hae := @rectifiable_sum_density_ae R n k c E hc hE hfin.
have he : measure_almost_equal HK thf (@metric_density R RNM k mu).
  rewrite /measure_almost_equal /measure_almost_everywhere.
  apply: (measure_null_subset hHm _ hae)=> x hna; split=> // hP; apply: hna.
  by exists (theta x); split.
have h1 : is_measure_density HK thf mu.
  rewrite {1}rectifiable_sum_measure_with_density; exact: measure_with_density_laws.
have h2 := @measure_density_almost_equal R RnM HK mu hHm thf (@metric_density R RNM k mu) h1 he.
apply: funext=> A; exact: (measure_density_unique h2 (measure_with_density_laws _ _) A).
Qed.
End WeightDensity.

Section Structure.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation RnM := (inner_metric_space hBn).
Local Notation GA := (projection_grassmann R n k).
Local Notation GB := (grassmann_bundle R n k).
Local Notation HK := (@hausdorff_measure R RnM k).
Local Notation tau mu := (@approximate_tangent_plane R n k mu).
Local Notation locrect E := (@is_locally_rectifiable_set R n k E).
Local Notation NX := (inner_norm_real_norm hBn).
Local Notation RNM := (real_norm_metric_space NX).

(** Source for [rectifiable_weight_representation]: Allard 3.1 and 3.5,
    p. 431: V ∈ RV_k(R^n) has a representation V = Σ_i c_i v(E_i) with
    ‖V‖ = Σ_i c_i H^k⌞E_i a Radon measure. Supporting lemma. *)
Lemma rectifiable_weight_representation (V : set GB -> \bar R) :
  is_rectifiable_varifold V ->
  exists (c : nat -> R) (E : nat -> set RnM), [/\ forall i, 0 < c i, forall i, locrect (E i),
    forall A, V A = nonnegative_sum [set: nat] (fun i => ((c i)%:E * set_varifold (E i) A)%E),
    varifold_weight V = @rectifiable_sum_measure R n k c E &
    is_measure (@rectifiable_sum_measure R n k c E) /\ is_radon_measure (@rectifiable_sum_measure R n k c E)].
Proof.
move=> hV; have [hm hr] := allard_3_1 hV.1.
have [c [E [hc hE hsum hw]]] := rectifiable_varifold_representation hV.
by exists c, E; split=> //; rewrite -hw.
Qed.

(** Source for [allard_3_5_1_b_tangent_ae]: Allard 3.5(1)(a), “only if”,
    p. 432: Tan^k(‖V‖, x) ∈ G(n, k) for ‖V‖ almost all x. Direct
    formalisation. *)
Theorem allard_3_5_1_b_tangent_ae (V : set GB -> \bar R) :
  is_rectifiable_varifold V ->
  measure_almost_everywhere (varifold_weight V)
    [set x | exists S, partial_function_graph (tau (varifold_weight V)) x S].
Proof.
move=> hV; have [c [E [hc hE _ -> [hm hr]]]] := rectifiable_weight_representation hV.
exact: rectifiable_sum_tangent_plane_ae hc hE hm hr.
Qed.

(** Source for [allard_3_5_1_b_measurable]: Allard 3.5(1)(b), p. 432:
    [x ↦ Tan^k(‖V‖, x)] is ‖V‖ measurable as a partial map into G(n, k).
    Direct formalisation. *)
Theorem allard_3_5_1_b_measurable (V : set GB -> \bar R) :
  is_rectifiable_varifold V ->
  is_measure_measurable_function (varifold_weight V) (tau (varifold_weight V)).
Proof.
move=> hV; have [c [E [hc hE _ -> [hm hr]]]] := rectifiable_weight_representation hV.
exact: rectifiable_sum_tangent_measurable hc hE hm hr.
Qed.

(** Source for [allard_3_5_1_b_pushforward]: Allard 3.5(1)(b), p. 432, with
    Federer 2.3.6, p. 77: there is a Borel map t of R^n into G(n, k) with
    t(x) = Tan^k(‖V‖, x) for ‖V‖ almost all x, and V is the image of ‖V‖
    under [x ↦ (x, t(x))]. Allard's standing hypothesis k ≤ n supplies a
    point of G(n, k). Direct formalisation. *)
Theorem allard_3_5_1_b_pushforward (V : set GB -> \bar R) : (k <= n)%N ->
  is_rectifiable_varifold V ->
  exists t : RnM -> GA, [/\ is_borel_function t,
    measure_almost_equal (varifold_weight V) (tau (varifold_weight V)) (partial_function_total t) &
    V = measure_pushforward (fun x : RnM => ((x, t x) : GB)) (varifold_weight V)].
Proof.
move=> hkn hV; have [c [E [hc hE hsum -> [hm hr]]]] := rectifiable_weight_representation hV.
have [S0 _] := @projection_grassmann_point R n k hkn.
have [t [ht [hae hi]]] := rectifiable_sum_tangent_borel_version hc hm hr
  (rectifiable_sum_tangent_agree hc hE hm hr) (rectifiable_sum_tangent_measurable hc hE hm hr) S0.
exists t; split=> //.
exact: rectifiable_varifold_pushforward hsum hi.
Qed.

(** Source for [allard_3_5_1_b_integral]: Allard 3.5(1)(b), p. 432:
    V(f) = ∫ f(x, Tan^k(‖V‖, x)) d‖V‖ x for every real valued Borel function
    f on G_k(R^n), as an equivalence of integral values (Federer 2.4.2,
    p. 81). Allard writes the right side as
    ∫ f(x, Tan^k(‖V‖, x)) Θ^k(‖V‖, x) dH^k x, which equals it by
    [allard_3_5_1_b_weight] and Federer 2.4.10; that form is not stated
    here. Direct formalisation. *)
Theorem allard_3_5_1_b_integral (V : set GB -> \bar R) (f : GB -> R) : (k <= n)%N ->
  is_rectifiable_varifold V ->
  is_borel_function (f : GB -> real_line_metric R) -> forall a,
  is_measure_integral V (real_total_integrand f) a <->
  is_measure_integral (varifold_weight V) (measure_tangent_integrand (varifold_weight V) f) a.
Proof.
move=> hkn hV hf a; have [c [E [hc hE hsum -> [hm hr]]]] := rectifiable_weight_representation hV.
exact: (rectifiable_varifold_integral hc hm hr (rectifiable_sum_tangent_agree hc hE hm hr)
  (rectifiable_sum_tangent_measurable hc hE hm hr) hkn hsum hf a).
Qed.

(** Source for [allard_3_5_1_b_weight]: Allard 3.5(1)(b), p. 432:
    ‖V‖ = H^k⌞Θ^k(‖V‖, ·), the measure of Federer 2.4.10, p. 85, with
    density the partial function Θ^k(‖V‖, ·) of Federer 2.10.19, p. 181, on
    all subsets of R^n. Direct formalisation. *)
Theorem allard_3_5_1_b_weight (V : set GB -> \bar R) : is_rectifiable_varifold V ->
  varifold_weight V = measure_with_density HK (@metric_density R RNM k (varifold_weight V)).
Proof.
move=> hV; have [c [E [hc hE _ -> [hm hr]]]] := rectifiable_weight_representation hV.
exact: rectifiable_sum_measure_metric_density hc hE hm hr.
Qed.

(** Source for [allard_3_5_1_a_only_if]: Allard 3.5(1)(a), “only if”,
    p. 432: if V ∈ RV_k(R^n), then 0 < Θ^k(‖V‖, x) < ∞ and
    Tan^k(‖V‖, x) ∈ G(n, k) for ‖V‖ almost all x. Direct formalisation. *)
Theorem allard_3_5_1_a_only_if (V : set GB -> \bar R) : is_rectifiable_varifold V ->
  measure_almost_everywhere (varifold_weight V)
    [set x | (exists t : R, 0 < t /\
        partial_function_graph (@metric_density R RNM k (varifold_weight V)) x t%:E) /\
      exists S, partial_function_graph (tau (varifold_weight V)) x S].
Proof.
move=> hV; have [c [E [hc hE _ -> [hm hr]]]] := rectifiable_weight_representation hV.
have hfin (K : set RnM) (hK : compact K) := radon_compact_finite hr hK.
have h1 := @rectifiable_sum_density_positive_finite R n k c E hc hE hfin.
have h2 := rectifiable_sum_tangent_plane_ae hc hE hm hr.
exact: (measure_almost_everywhere_and hm h1 h2).
Qed.

(** Source for [allard_3_5_1_b]: Allard 3.5(1)(b), p. 432: for
    V ∈ RV_k(R^n), ‖V‖ = H^k⌞Θ^k(‖V‖, ·), [x ↦ Tan^k(‖V‖, x)] is ‖V‖
    measurable, and V(f) = ∫ f(x, Tan^k(‖V‖, x)) d‖V‖ x for every real
    valued Borel function f on G_k(R^n). Direct formalisation. *)
Theorem allard_3_5_1_b (V : set GB -> \bar R) : (k <= n)%N -> is_rectifiable_varifold V ->
  [/\ varifold_weight V = measure_with_density HK (@metric_density R RNM k (varifold_weight V)),
    is_measure_measurable_function (varifold_weight V) (tau (varifold_weight V)) &
    forall f : GB -> R, is_borel_function (f : GB -> real_line_metric R) -> forall a,
      is_measure_integral V (real_total_integrand f) a <->
      is_measure_integral (varifold_weight V) (measure_tangent_integrand (varifold_weight V) f) a].
Proof.
move=> hkn hV; split.
- exact: allard_3_5_1_b_weight.
- exact: allard_3_5_1_b_measurable.
- by move=> f hf a; exact: allard_3_5_1_b_integral.
Qed.
End Structure.
