(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint proof
    of thm:main: the measure facts used in the cut-off argument.

    For a set M ⊆ R^n and a function f : R^n → R with f ≥ 0 on M, the
    measure μ_f = (H^k ⌞ M) ⌞ f of Federer 2.4.10 is
    [dgpr_main_measure k M f] (DgprMainHypotheses.v). This file proves
    that μ_f is a measure for which the Borel sets are measurable and
    the H^k ⌞ M measurable functions are measurable
    ([dgpr_density_measure_is_measure], [dgpr_density_measure_borel],
    [dgpr_density_measure_function]); that μ_f is finite if f is
    H^k ⌞ M summable ([dgpr_density_measure_finite]); that μ_f(A) = 0
    if f = 0 on M ∩ A ([dgpr_density_measure_zero]); that μ_f(A) ≤ μ_g(R^n)
    if f ≤ g on M ∩ A and g ≥ 0 on M ([dgpr_density_measure_compare]);
    and that ∫ F dμ_{w f} = ∫ w F dμ_f for H^k ⌞ M measurable w ≥ 0 and
    F ([dgpr_density_measure_change]). In the proof of thm:main these
    facts are applied with f = θ and w = φ_ϱ.

    It also proves that A • B is measurable whenever the maps A and B
    with values in Hom(R^n, Y) are measurable
    ([dgpr_hom_pairing_measurable]); that the product and the difference
    of two measurable real functions are measurable
    ([dgpr_real_total_multiply_measurable],
    [dgpr_real_total_subtract_measurable]); and that a measurable
    function bounded almost everywhere by K with respect to a measure of
    finite total mass m is summable with integral at most K m
    ([dgpr_bounded_integral]). *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals
  constructive_ereal topology ring.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm InnerProductLaws
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LinearBasis
  HomInner HomCompositionDeterminant InnerMetric InnerSpaceCountableBase InnerOwnNormTopology
  HomeomorphismUP HomeomorphicCountableBase CountableOpenBaseUP CountableBaseMeasurablePair
  NormBoundedBilinearUP BoundedBilinearContinuity InnerNormalizationSmooth RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialFunctionPair PartialFunctionPostcomposition
  PartialZeroExtension PartialZeroExtensionLaws PartialFunctionExtensionality PartialExtendedOrderLoci
  PartialDensityProduct PartialAbsolutePartsGraph MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureRestriction
  MeasureDensityUP MeasureDensity MeasureDensityNullSets MeasureDensityTransfer MeasureSubsetIntegral
  MeasureChangeOfDensity DensityCharacteristicIntegral MeasurableFunctionUP MeasurablePostcomposition
  MeasurableGraphEquivalence MeasurableRealArithmetic MeasureStepIntegralIdentification
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence MeasureIntegralComparison
  MeasureAbsoluteSummability MeasureUpperIntegralMonotone MeasureUpperAlmostEquality FiniteMeasureBoundedNorm
  SummableRealFunctionUP RealTotalMeasurabilityProjection BorelRegularMeasureUP TopologicalBorel
  BorelFunctionUP BorelFunctionBasic HausdorffMeasure HausdorffClosedCoverAgreement MetricClosedBalls.
From DPGPR Require Import DgprMichaelSimon DgprVarifoldWeight DgprMainHypotheses.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Pairing.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation heX := (@coordinate_basisP R n).
Variable Y : lmodType R.
Variable CY : Y -> Y -> R.
Hypothesis hCY : is_inner_product CY.
Variable d : nat.
Variable eY : 'I_d -> Y.
Hypothesis heY : is_basis eY.
Local Notation BH := (hom_inner_productP BX hCY heX).
Local Notation HI := (hom_inner BX hCY heX).
Local Notation hNH := (inner_norm_real_norm BH).
Local Notation HT := (real_norm_metric_space hNH).

(** Source for [dgpr_hom_countable_open_base]: Federer 2.7.16, p. 136,
    and 2.5.14, p. 107: the space Hom(R^n, Y), normed by |·| of Federer
    1.7.9, has a countable base of open sets, since it is a finite
    dimensional inner product space ([inner_space_countable_open_base])
    with the base of the maps [x ↦ e_i^*(x) e'_j]
    ([hom_rank_one_baseP]). Supporting lemma. *)
Lemma dgpr_hom_countable_open_base : exists U : nat -> set HT, is_countable_open_base U.
Proof.
have [U hU] := inner_space_countable_open_base BH (hom_rank_one_baseP heX heY).
have hHomeo := inner_own_norm_homeomorphism BH.
exists (fun i => U i).
exact: (homeomorphic_countable_base (homeomorphism_left_inverse hHomeo)
  (homeomorphism_right_inverse hHomeo) (homeomorphism_continuous hHomeo)
  (homeomorphism_inverse_continuous hHomeo) hU).
Qed.

(** Source for [dgpr_hom_pairing_measurable]: Federer 2.3.2(4), p. 73,
    with 2.3.2(9), p. 74, for the pair of maps into a space with a
    countable base: if A and B are μ measurable maps with values in
    Hom(R^n, Y), then [x ↦ A(x) • B(x)] is μ measurable, since the
    inner product is continuous. Supporting lemma. *)
Lemma dgpr_hom_pairing_measurable (T : choiceType) (mu : set T -> \bar R) (hm : is_measure mu)
    (F G : T -> Hom X Y) :
  is_measure_measurable_function mu (partial_function_total (fun x => (F x : HT))) ->
  is_measure_measurable_function mu (partial_function_total (fun x => (G x : HT))) ->
  is_measure_measurable_function mu (real_total_integrand (fun x => HI (F x) (G x))).
Proof.
move=> hF hG.
have [U hU] := dgpr_hom_countable_open_base.
have hp := countable_base_measurable_pair hm hU hU hF hG.
have hc : continuous (fun p : (HT * HT)%type => (HI p.1 p.2 : real_line_metric R)).
  apply: dgpr_real_norm_line_continuous.
  have h1 : continuous (fun p : (HT * HT)%type => (p.1 : HT)) by move=> p; apply: cvg_fst.
  have h2 : continuous (fun p : (HT * HT)%type => (p.2 : HT)) by move=> p; apply: cvg_snd.
  exact: (@bounded_bilinear_continuous_factors R _ _ R^o _ _ _ hNH hNH (@scalar_absolute_value_norm R)
    HI (inner_product_norm_bounded_bilinear BH) _ (fun p : (HT * HT)%type => p.1)
    (fun p : (HT * HT)%type => p.2) h1 h2).
have hb := measurable_function_borel_postcomposition hm hp (continuous_borel_function hc).
apply: (@measurable_partial_real_embedding R T mu hm).
apply: (@measurable_function_graph_equivalent R T _ mu _ _ _ hb) => x z; split.
- move=> [[u v] [[hu hv] he]].
  have hu' : F x = u := hu.
  have hv' : G x = v := hv.
  change (HI (F x) (G x) = z); by rewrite hu' hv'.
- move=> he; exists (F x, G x); by split; [split|].
Qed.

End Pairing.

Section RealTotal.
Variable R : realType.
Variable T : choiceType.
Variable mu : set T -> \bar R.
Hypothesis hm : is_measure mu.

(** Source for [dgpr_real_total_multiply_measurable]: Federer 2.3.2(9),
    p. 74: the product of two μ measurable real functions is μ
    measurable. Supporting lemma. *)
Lemma dgpr_real_total_multiply_measurable (f g : T -> R) :
  is_measure_measurable_function mu (real_total_integrand f) ->
  is_measure_measurable_function mu (real_total_integrand g) ->
  is_measure_measurable_function mu (real_total_integrand (fun x => f x * g x)).
Proof.
move=> hf hg.
have h := measurable_real_function_multiply hm (real_total_measurability_projection hm hf)
  (real_total_measurability_projection hm hg).
apply: (@measurable_partial_real_embedding R T mu hm).
apply: (@measurable_function_graph_equivalent R T _ mu _ _ _ h) => x z; split.
- move=> [[u v] [[hu hv] he]].
  have hu' : f x = u := hu.
  have hv' : g x = v := hv.
  change (f x * g x = z); by rewrite hu' hv'.
- move=> he; exists (f x, g x); by split; [split|].
Qed.

(** Source for [dgpr_real_total_subtract_measurable]: Federer 2.3.2(9),
    p. 74: the difference of two μ measurable real functions is μ
    measurable. Supporting lemma. *)
Lemma dgpr_real_total_subtract_measurable (f g : T -> R) :
  is_measure_measurable_function mu (real_total_integrand f) ->
  is_measure_measurable_function mu (real_total_integrand g) ->
  is_measure_measurable_function mu (real_total_integrand (fun x => f x - g x)).
Proof.
move=> hf hg.
have h := measurable_real_function_subtract hm (real_total_measurability_projection hm hf)
  (real_total_measurability_projection hm hg).
apply: (@measurable_partial_real_embedding R T mu hm).
apply: (@measurable_function_graph_equivalent R T _ mu _ _ _ h) => x z; split.
- move=> [[u v] [[hu hv] he]].
  have hu' : f x = u := hu.
  have hv' : g x = v := hv.
  change (f x - g x = z); by rewrite hu' hv'.
- move=> he; exists (f x, g x); by split; [split|].
Qed.

(** Source for [dgpr_bounded_integral]: Federer 2.4.4(5), p. 82, and
    2.4.3(2), p. 81: if μ(T) = m < ∞, f is μ measurable and |f| ≤ K
    μ almost everywhere, then f is μ summable and ∫ f dμ ≤ K m.
    Supporting lemma. *)
Lemma dgpr_bounded_integral (m : R) (f : T -> R) (K : R) (A : set T) :
  mu setT = m%:E -> measure_almost_everywhere mu A ->
  is_measure_measurable_function mu (real_total_integrand f) ->
  (forall x, A x -> `|f x| <= K) ->
  exists b : R, is_measure_integral mu (real_total_integrand f) b%:E /\ b <= K * m.
Proof.
move=> hmu hA hf hK.
have hc : is_measure_integral mu (real_total_integrand (fun _ : T => K)) (K * m)%:E.
  apply: (measure_integral_graph_equivalent _ (@finite_measure_constant_integral R T mu hm m K hmu)).
  move=> x z; split.
  - by move=> hz; apply/real_total_integrand_graph; exact: hz.
  - by move=> /real_total_integrand_graph hz.
have hle : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_extended_function_absolute_value (real_total_integrand f))
    (real_total_integrand (fun _ : T => K))).
  apply: (measure_almost_everywhere_mono hm _ hA) => x hx.
  exists (`|f x|)%:E, K%:E; split.
    exists (f x)%:E; split; first exact/real_total_integrand_graph.
    by rewrite abse_EFin.
  split; first exact/real_total_integrand_graph.
  by rewrite lee_fin; exact: hK.
have [[b hb] _] := measure_dominated_summable hm hf (ex_intro _ (K * m) hc) hle.
exists b; split=> //.
rewrite -lee_fin; apply: (measure_integral_monotone hm hb hc).
apply: (measure_almost_everywhere_mono hm _ hA) => x hx.
exists (f x)%:E, K%:E; split; first exact/real_total_integrand_graph.
split; first exact/real_total_integrand_graph.
by rewrite lee_fin; apply: le_trans (hK x hx); exact: ler_norm.
Qed.

End RealTotal.

Section DensityMeasure.
Variable R : realType.
Variables n k : nat.
Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation RnM := (inner_metric_space BX).
Local Notation HK := (@hausdorff_measure R RnM k).
Variable M : set RnM.
Local Notation HM := (measure_restrict HK M).

Let hHm : is_measure HK := hausdorff_measure_is_measure RnM k.
Let hHMm : is_measure HM := measure_restrict_is_measure hHm M.

(** Source for [dgpr_restrict_on]: Federer 2.1.2, p. 54:
    (H^k ⌞ M)(R^n ∖ M) = 0. Supporting lemma. *)
Lemma dgpr_restrict_on : measure_almost_everywhere HM M.
Proof. by rewrite /measure_almost_everywhere /measure_restrict setICr (measure_empty hHm). Qed.

(** Source for [dgpr_restrict_borel]: Federer 2.10.1, p. 171, 2.1.2,
    p. 54, and 2.1.3, p. 55: the Borel subsets of R^n are H^k ⌞ M
    measurable, since H^k is Borel regular. Supporting lemma. *)
Lemma dgpr_restrict_borel (A : set RnM) : borel_set A -> measure_measurable HM A.
Proof.
move=> hA; apply: measure_restrict_measurable.
exact: (borel_regular_borel_measurable hHm (hausdorff_measure_borel_regular RnM k) hA).
Qed.

Variable f : X -> R.
Hypothesis hf : forall x, M x -> 0 <= f x.
Local Notation mu := (dgpr_main_measure k M f).

Let hlaws : is_measure_density HM (real_total_integrand f) mu :=
  measure_with_density_laws HM (real_total_integrand f).

Let hpos : measure_almost_everywhere HM
    (partial_extended_nonnegative_locus (real_total_integrand f)).
Proof.
apply: (measure_almost_everywhere_mono hHMm _ dgpr_restrict_on) => x hx.
exists (f x)%:E; split; first exact/real_total_integrand_graph.
by rewrite lee_fin; exact: hf.
Qed.

(** Source for [dgpr_density_measure_is_measure]: Federer 2.4.10,
    p. 85: μ_f = (H^k ⌞ M) ⌞ f is a measure, since f ≥ 0 on M.
    Supporting lemma. *)
Lemma dgpr_density_measure_is_measure : is_measure mu.
Proof.
exact: (@measure_with_density_is_measure R RnM HM hHMm (real_total_integrand f) hpos).
Qed.

(** Source for [dgpr_density_measure_borel]: Federer 2.4.10, p. 85:
    the Borel subsets of R^n are μ_f measurable. Supporting lemma. *)
Lemma dgpr_density_measure_borel (A : set RnM) : borel_set A -> measure_measurable mu A.
Proof.
move=> hA.
exact: (@measure_with_density_measurable R RnM HM hHMm (real_total_integrand f) A hpos
  (dgpr_restrict_borel hA)).
Qed.

(** Source for [dgpr_density_measure_function]: Federer 2.4.10, p. 85:
    an H^k ⌞ M measurable function is μ_f measurable. Supporting
    lemma. *)
Lemma dgpr_density_measure_function (Z : topologicalType) (g : partial_function RnM Z) :
  is_measure_measurable_function HM g -> is_measure_measurable_function mu g.
Proof. exact: (measure_density_measurable_function hHMm hlaws hpos). Qed.

(** Source for [dgpr_density_measure_on]: Federer 2.4.10, p. 85:
    μ_f(R^n ∖ M) = 0. Supporting lemma. *)
Lemma dgpr_density_measure_on : measure_almost_everywhere mu M.
Proof. exact: (measure_density_null_set hHMm hlaws dgpr_restrict_on). Qed.

(** Source for [dgpr_density_measure_finite]: Federer 2.4.10, p. 85:
    μ_f(R^n) = ∫ f d(H^k ⌞ M) is a real number if f is H^k ⌞ M
    summable. Supporting lemma. *)
Lemma dgpr_density_measure_finite :
  summable_real_functions HM f -> exists a : R, mu setT = a%:E.
Proof.
move=> [a ha].
have hT : measure_measurable HM setT.
  by apply: dgpr_restrict_borel; apply: closed_borel_set; exact: closedT.
have hs := measurable_density_subset_integral hHMm hlaws hpos ha.1 hT.
have hext : partial_function_zero_extension (0 : extended_real_line R) setT
    (real_total_integrand f) = real_total_integrand f.
  apply: partial_function_graph_extensionality => x z.
  exact: partial_zero_extension_whole_graph.
rewrite /is_measure_subset_integral hext in hs.
by exists a; exact: (measure_integral_unique hs ha).
Qed.

(** Source for [dgpr_density_measure_zero]: Federer 2.4.10, p. 85, and
    2.4.3(2), p. 81: μ_f(A) = 0 whenever f = 0 on M ∩ A. Supporting
    lemma. *)
Lemma dgpr_density_measure_zero (A : set RnM) :
  (forall x, M x -> A x -> f x = 0) -> mu A = 0%E.
Proof.
move=> hA; rewrite (hlaws A) /measure_subset_upper_integral.
have heq : measure_almost_equal HM
    (partial_function_zero_extension (0 : extended_real_line R) A (real_total_integrand f))
    (partial_function_total (fun _ : RnM => (0 : extended_real_line R))).
  apply: (measure_almost_everywhere_mono hHMm _ dgpr_restrict_on) => x hx.
  exists 0%E; split=> //; apply/partial_function_zero_extension_graph.
  have [hxA|hxA] := pselect (A x).
    left; split=> //; apply/real_total_integrand_graph.
    by rewrite (hA x hx hxA).
  by right.
rewrite (@measure_upper_integral_almost_equal R RnM HM hHMm _ _ heq).
exact: measure_upper_extended_zero.
Qed.

(** Source for [dgpr_density_measure_compare]: Federer 2.4.10, p. 85,
    and 2.4.3(2), p. 81: μ_f(A) ≤ μ_g(R^n) whenever f ≤ g on M ∩ A and
    g ≥ 0 on M. Supporting lemma. *)
Lemma dgpr_density_measure_compare (g : X -> R) (A : set RnM) :
  (forall x, M x -> A x -> f x <= g x) -> (forall x, M x -> 0 <= g x) ->
  (mu A <= dgpr_main_measure k M g setT)%E.
Proof.
move=> hfg hg.
rewrite (hlaws A).
change (dgpr_main_measure k M g setT) with (measure_with_density HM (real_total_integrand g) setT).
rewrite (measure_with_density_laws HM (real_total_integrand g) setT).
rewrite /measure_subset_upper_integral; apply: (measure_upper_integral_monotone hHMm).
apply: (measure_almost_everywhere_mono hHMm _ dgpr_restrict_on) => x hx.
have hgx : partial_function_graph (partial_function_zero_extension (0 : extended_real_line R)
    setT (real_total_integrand g)) x (g x)%:E.
  by apply/partial_zero_extension_whole_graph; exact/real_total_integrand_graph.
have [hxA|hxA] := pselect (A x).
  exists (f x)%:E, (g x)%:E; split.
    by apply/partial_function_zero_extension_graph; left; split=> //;
      exact/real_total_integrand_graph.
  by split=> //; rewrite lee_fin; exact: hfg.
exists 0%E, (g x)%:E; split.
  by apply/partial_function_zero_extension_graph; right.
by split=> //; rewrite lee_fin; exact: hg.
Qed.

(** Source for [dgpr_density_product_summable]: Federer 2.4.4(5),
    p. 82: if f is H^k ⌞ M summable, w is H^k ⌞ M measurable and
    0 ≤ w ≤ 1 on M, then w f is H^k ⌞ M summable. Supporting lemma. *)
Lemma dgpr_density_product_summable (w : X -> R) :
  summable_real_functions HM f ->
  is_measure_measurable_function HM (real_total_integrand w) ->
  (forall x, M x -> 0 <= w x <= 1) -> summable_real_functions HM (fun x => w x * f x).
Proof.
move=> hs hw hw1.
have hm : is_measure_measurable_function HM (real_total_integrand (fun x => w x * f x)).
  have [a ha] := hs.
  exact: (@dgpr_real_total_multiply_measurable R RnM HM hHMm w f hw ha.1).
have hle : measure_almost_everywhere HM (partial_extended_le_locus
    (partial_extended_function_absolute_value (real_total_integrand (fun x => w x * f x)))
    (real_total_integrand f)).
  apply: (measure_almost_everywhere_mono hHMm _ dgpr_restrict_on) => x hx.
  exists (`|w x * f x|)%:E, (f x)%:E; split.
    exists (w x * f x)%:E; split; first exact/real_total_integrand_graph.
    by rewrite abse_EFin.
  split; first exact/real_total_integrand_graph.
  have /andP [hw0 hw1'] := hw1 x hx.
  have hfx : 0 <= f x by apply: hf.
  rewrite lee_fin normrM (ger0_norm hw0) (ger0_norm hfx).
  by rewrite -[X in _ <= X]mul1r ler_wpM2r.
by have [h _] := measure_dominated_summable hHMm hm hs hle.
Qed.

(** Source for [dgpr_density_measure_change]: Federer 2.4.10, p. 85,
    applied twice: if f is H^k ⌞ M summable, w and F are H^k ⌞ M
    measurable, w ≥ 0 on M, and w F is μ_f summable with integral b,
    then F is μ_{w f} summable with integral b, since both integrals
    equal ∫ w f F d(H^k ⌞ M). Supporting lemma. *)
Lemma dgpr_density_measure_change (w F : X -> R) (b : R) :
  summable_real_functions HM f ->
  is_measure_measurable_function HM (real_total_integrand w) -> (forall x, M x -> 0 <= w x) ->
  is_measure_measurable_function HM (real_total_integrand F) ->
  is_measure_integral mu (real_total_integrand (fun x => w x * F x)) b%:E ->
  is_measure_integral (dgpr_main_measure k M (fun x => w x * f x)) (real_total_integrand F) b%:E.
Proof.
move=> [a ha] hw hw0 hF hb.
have hfm := ha.1.
have hwfm : is_measure_measurable_function HM (real_total_integrand (fun x => w x * f x)).
  exact: (@dgpr_real_total_multiply_measurable R RnM HM hHMm w f hw hfm).
have hwFm : is_measure_measurable_function HM (real_total_integrand (fun x => w x * F x)).
  exact: (@dgpr_real_total_multiply_measurable R RnM HM hHMm w F hw hF).
have hwpos : measure_almost_everywhere HM
    (partial_extended_nonnegative_locus (real_total_integrand (fun x => w x * f x))).
  apply: (measure_almost_everywhere_mono hHMm _ dgpr_restrict_on) => x hx.
  exists (w x * f x)%:E; split; first exact/real_total_integrand_graph.
  have hfx : 0 <= f x by apply: hf.
  by rewrite lee_fin mulr_ge0 // hw0.
have h1 := (measure_density_integral_iff hHMm hlaws hfm hpos hwFm b%:E).1 hb.
apply/(measure_density_integral_iff hHMm (measure_with_density_laws HM _) hwfm hwpos hF b%:E).
suff -> : partial_density_product (real_total_integrand F) (real_total_integrand (fun x => w x * f x)) =
    partial_density_product (real_total_integrand (fun x => w x * F x)) (real_total_integrand f).
  exact: h1.
apply: partial_function_graph_extensionality => x z.
rewrite !partial_density_product_graph; split.
- move=> [u [v [/real_total_integrand_graph hu [/real_total_integrand_graph hv he]]]].
  exists (w x * F x)%:E, (f x)%:E; split; first exact/real_total_integrand_graph.
  split; first exact/real_total_integrand_graph.
  by rewrite -he -hu -hv -!EFinM; congr EFin; ring.
- move=> [u [v [/real_total_integrand_graph hu [/real_total_integrand_graph hv he]]]].
  exists (F x)%:E, (w x * f x)%:E; split; first exact/real_total_integrand_graph.
  split; first exact/real_total_integrand_graph.
  by rewrite -he -hu -hv -!EFinM; congr EFin; ring.
Qed.

End DensityMeasure.

Section Balls.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation RnM := (inner_metric_space BX).

(** Source for [dgpr_open_ball_open]: Federer 2.2.8, p. 64: the ball
    R^n ∩ { y : |y| < r } is open. Supporting lemma. *)
Lemma dgpr_open_ball_open (r : R) : open [set y : RnM | N y < r].
Proof.
have -> : [set y : RnM | N y < r] = [set y : RnM | mdist (0 : RnM) y < r].
  apply/seteqP; split=> y; by rewrite /= inner_metric_distanceE sub0r inner_normN.
exact: metric_open_ball_open.
Qed.

End Balls.
