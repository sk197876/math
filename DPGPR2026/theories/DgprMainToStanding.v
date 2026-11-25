(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint proof
    of lem:compact_case, first paragraph: the passage from the data of
    mr:hypotheses_main ([dgpr_main_hypotheses], DgprMainHypotheses.v) to
    the hypotheses (S) of mr:standing ([dgpr_standing], DgprStanding.v).

    Let μ = (H^k ⌞ M) ⌞ θ and a = μ(R^n) with 0 < a < ∞. The blueprint
    replaces θ by θ/a and Υ by Υ/a; then μ becomes a^{-1} μ, the
    measure c φ of Federer 2.7.18, p. 141 ([measure_scale]), and ‖Υ‖ becomes
    a^{-1} ‖Υ‖ ([dgpr_variation_value_scale], [dgpr_measure_scale_radon]).
    The map X is extended to R^n by a value A_0 ∈ K on R^n ∖ M
    ([dgpr_main_extension]); since μ(R^n ∖ M) = 0, the extension is
    μ measurable and satisfies the constraint Υ(g) = −σ(Dg). The
    measure facts used are collected in [dgpr_main_measure_is_measure],
    [dgpr_main_measure_open], [dgpr_main_measure_function],
    [dgpr_main_measure_finite] and [dgpr_main_measure_hausdorff]. Given a
    dual density dΥ of ‖Υ‖ ([dgpr_dual_density], DgprDualDensity.v), the
    hypotheses (S) hold for the normalised data with T = 1 and
    μ_0 = a^{-1} μ ([dgpr_main_standing]); the choice of μ_0 = μ ⌞ E is
    made in DgprCompactCaseGeneral.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LinearBasis HomInner ScalarInnerProduct
  InnerConvex InnerMetric PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic MeasureAlmostUP
  MeasureAlmostBasic MeasureRestriction MeasureDensity MeasureDensityUP MeasureDensityNullSets
  MeasurableFunctionUP MeasurableAlmostModification MeasureIntegralUP MeasureIntegralAlmostEquality
  MeasureIntegralUniqueness MeasureSubsetIntegral SummableRealFunctionUP RadonMeasureUP FunctionLatticeUP
  CompactSupportFunctionUP ExtendedSupremumUP DistributionVariationUP RealValueSupremumScaling
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation NormDifferentialUP HausdorffMeasure
  HausdorffClosedCoverAgreement BorelRegularMeasureUP TopologicalBorel RectifiableSetUP
  MeasureScaleIntegral EuclideanDistributionMeasureContext PartialZeroExtension PartialZeroExtensionLaws
  PartialExtendedOrderLoci PartialFunctionExtensionality DensityCharacteristicIntegral
  ExtendedRealOrderTopology.
From DPGPR Require Import DgprSingularValue DgprStanding DgprMainHypotheses.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section MeasureScaleRadon.
Variable R : realType.
Variable T : topologicalType.
Variable mu : set T -> \bar R.
Hypothesis hm : is_measure mu.
Hypothesis hr : is_radon_measure mu.
Variable c : R.
Hypothesis hc : 0 < c.

(** Source for [dgpr_measure_scale_radon]: Federer 2.2.5, p. 62, and
    2.7.18, p. 141: the measure c φ is a Radon measure whenever φ is one
    and 0 < c; supporting the normalisation of ‖Υ‖ in the proof of
    blueprint lem:compact_case. *)
Lemma dgpr_measure_scale_radon : is_radon_measure (measure_scale c mu).
Proof.
have hcE : (0 <= c%:E)%E by rewrite lee_fin ltW.
have hciE : (0 <= c^-1%:E)%E by rewrite lee_fin invr_ge0 ltW.
have hcc (b : \bar R) : (c%:E * (c^-1%:E * b))%E = b.
  by rewrite muleA -EFinM mulfV ?gt_eqF // mul1e.
have hcc' (b : \bar R) : (c^-1%:E * (c%:E * b))%E = b.
  by rewrite muleA -EFinM mulVf ?gt_eqF // mul1e.
constructor.
- exact: radon_hausdorff hr.
- exact: radon_locally_compact hr.
- move=> K hK; apply/(measure_scale_finite hm hc); exact: radon_compact_finite hr K hK.
- move=> V hV; exact: (measure_scale_measurable hm c (radon_open_measurable hr hV)).
- move=> V hV b hb; rewrite /measure_scale -(hcc b); apply: lee_wpmul2l => //.
  apply: (radon_inner_least hr hV) => K hK hKV.
  rewrite -(hcc' (mu K)); apply: lee_wpmul2l => //; exact: hb K hK hKV.
- move=> A b hb; rewrite /measure_scale -(hcc b); apply: lee_wpmul2l => //.
  apply: (radon_outer_greatest hr) => V hV hAV.
  rewrite -(hcc' (mu V)); apply: lee_wpmul2l => //; exact: hb V hV hAV.
Qed.
End MeasureScaleRadon.

Section VariationScale.
Variable R : realType.
Variable X : choiceType.
Variable Y : lmodType R.
Variable NY : Y -> R.
Variable E : lmodType R.
Variable value : Hom E (GRing.Lmodule.clone R (X -> Y) _).
Variable S : Hom E R^o.

(** Source for [dgpr_variation_value_scale]: Federer 4.1.5, p. 349:
    the variation satisfies ‖c S‖(f) = c ‖S‖(f) for 0 < c, since the
    admissible values S'(φ) for c S are c times those for S; supporting
    the normalisation Υ/μ(R^n) in the proof of blueprint
    lem:compact_case. *)
Lemma dgpr_variation_value_scale (f : X -> R) (b : \bar R) (c : R) : 0 < c ->
  is_distribution_variation_value NY value S f b ->
  is_distribution_variation_value NY value (c *: S) f (c%:E * b)%E.
Proof.
move=> hc hb.
have e : distribution_variation_values NY value (c *: S) f =
    (fun r : R => c * r) @` distribution_variation_values NY value S f.
  apply/seteqP; split.
  - by move=> r [phi [hphi <-]]; exists (S phi); first by exists phi.
  - by move=> r [s [phi [hphi <-]] <-]; exists phi; split.
rewrite /is_distribution_variation_value e.
exact: real_value_supremum_positive_scale.
Qed.
End VariationScale.

Section MainMeasure.
Variable R : realType.
Variables n k : nat.
Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation NT := (real_norm_metric_space hN).
Local Notation RnM := (inner_metric_space BX).
Local Notation HK := (@hausdorff_measure R RnM k).
Variable M : set RnM.
Variable theta : X -> R.
Hypothesis htheta : forall x, M x -> 0 <= theta x.
Hypothesis hsum : summable_real_functions (measure_restrict HK M) theta.
Local Notation HM := (measure_restrict HK M).
Local Notation mu := (dgpr_main_measure k M theta).

Let hHm : is_measure HK := hausdorff_measure_is_measure RnM k.
Let hHMm : is_measure HM := measure_restrict_is_measure hHm M.
Let hlaws : is_measure_density HM (real_total_integrand theta) mu :=
  measure_with_density_laws HM (real_total_integrand theta).

Let hpos : measure_almost_everywhere HM
    (partial_extended_nonnegative_locus (real_total_integrand theta)).
Proof.
rewrite /measure_almost_everywhere /measure_restrict.
rewrite (_ : M `&` ~` _ = set0) ?(measure_empty hHm) //.
apply/seteqP; split=> // x [hxM hx]; apply: hx; exists (theta x)%:E; split.
  by exists (theta x).
by rewrite lee_fin; exact: htheta.
Qed.

(** Source for [dgpr_main_measure_is_measure]: Federer 2.4.10, p. 85:
    the set function μ = (H^k ⌞ M) ⌞ θ is a measure, since θ ≥ 0 on M;
    blueprint mr:hypotheses_main. *)
Lemma dgpr_main_measure_is_measure : is_measure mu.
Proof.
exact: (@measure_with_density_is_measure R RnM HM hHMm (real_total_integrand theta) hpos).
Qed.

(** Source for [dgpr_main_measure_null]: Federer 2.4.10, p. 85:
    μ(A) = 0 whenever H^k(M ∩ A) = 0, that is, μ is absolutely
    continuous with respect to H^k ⌞ M; proof of blueprint
    lem:compact_case. *)
Lemma dgpr_main_measure_null (A : set RnM) : HK (M `&` A) = 0%E -> mu A = 0%E.
Proof. by move=> h; apply: (measure_density_null_set hHMm hlaws). Qed.

(** Source for [dgpr_main_measure_on]: the set R^n ∖ M is μ null, by
    [dgpr_main_measure_null]; proof of blueprint lem:compact_case. *)
Lemma dgpr_main_measure_on : measure_almost_everywhere mu M.
Proof.
apply: dgpr_main_measure_null; rewrite setICr; exact: measure_empty hHm.
Qed.

(** Source for [dgpr_main_measure_measurable]: Federer 2.4.10, p. 85:
    the H^k ⌞ M measurable sets are μ measurable; proof of blueprint
    lem:compact_case. *)
Lemma dgpr_main_measure_measurable (A : set RnM) :
  measure_measurable HM A -> measure_measurable mu A.
Proof.
exact: (@measure_with_density_measurable R RnM HM hHMm (real_total_integrand theta) A hpos).
Qed.

(** Source for [dgpr_main_measure_open]: the open subsets of R^n are
    μ measurable, since they are Borel sets, H^k is Borel regular
    (Federer 2.10.2(1), p. 171), and H^k ⌞ M and (H^k ⌞ M) ⌞ θ inherit
    the measurable sets (2.1.2, p. 54; 2.4.10, p. 85); hypotheses (S),
    "μ is a Borel measure", in the proof of blueprint lem:compact_case. *)
Lemma dgpr_main_measure_open (A : set NT) : open A -> measure_measurable mu A.
Proof.
move=> hA; apply: dgpr_main_measure_measurable; apply: measure_restrict_measurable.
apply: (borel_regular_borel_measurable hHm (hausdorff_measure_borel_regular RnM k)).
apply: open_borel_set.
exact: (proj1 (continuousP _) (@euclidean_distribution_inner_to_norm R n) A hA).
Qed.

(** Source for [dgpr_main_measure_function]: Federer 2.3.2, p. 73, and
    2.4.10, p. 85: an H^k ⌞ M measurable function is μ measurable; proof
    of blueprint lem:compact_case. *)
Lemma dgpr_main_measure_function (Z : topologicalType) (f : partial_function RnM Z) :
  is_measure_measurable_function HM f -> is_measure_measurable_function mu f.
Proof.
move=> [hd ho]; split.
  exact: (@measure_density_almost_everywhere R RnM HM mu hHMm (real_total_integrand theta) _
    hlaws hd).
move=> U hU; exact: dgpr_main_measure_measurable (ho U hU).
Qed.

(** Source for [dgpr_main_measure_finite]: the number
    μ(R^n) = ∫ θ d(H^k ⌞ M) is finite, since θ is H^k ⌞ M summable
    (Federer 2.4.10, p. 85); proof of blueprint lem:compact_case. *)
Lemma dgpr_main_measure_finite : exists a : R, mu setT = a%:E.
Proof.
have [a ha] := hsum.
have hT : measure_measurable HM setT.
  apply: measure_restrict_measurable.
  apply: (borel_regular_borel_measurable hHm (hausdorff_measure_borel_regular RnM k)).
  apply: closed_borel_set; exact: closedT.
have hs := measurable_density_subset_integral hHMm hlaws hpos ha.1 hT.
have hext : partial_function_zero_extension (0 : extended_real_line R) setT
    (real_total_integrand theta) = real_total_integrand theta.
  apply: partial_function_graph_extensionality => x z.
  exact: partial_zero_extension_whole_graph.
rewrite /is_measure_subset_integral hext in hs.
by exists a; exact: (measure_integral_unique hs ha).
Qed.

(** Source for [dgpr_main_measure_hausdorff]: proof of blueprint
    lem:compact_case, "since μ is absolutely continuous with respect to
    H^k, we have 0 < H^k(E)": if 0 < μ(A), then 0 < H^k(A). *)
Lemma dgpr_main_measure_hausdorff (A : set RnM) : (0 < mu A)%E -> (0 < HK A)%E.
Proof.
move=> h; rewrite lt_neqAle (measure_nonnegative hHm) andbT; apply/eqP => e.
have h0 : HK (M `&` A) = 0%E.
  by apply: (measure_null_subset hHm (@subIsetr _ M A)); rewrite -e.
by rewrite (dgpr_main_measure_null h0) ltxx in h.
Qed.
End MainMeasure.

Section Extension.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Variable Y : lmodType R.

(** Source for [dgpr_main_extension]: proof of blueprint
    lem:compact_case, "extend X to R^n by a constant value in K on
    R^n ∖ M": the map equal to X on M and to A_0 on R^n ∖ M.
    Definition. *)
Definition dgpr_main_extension (M : set X) (Xf : X -> Hom X Y) (A0 : Hom X Y) (x : X) : Hom X Y :=
  if pselect (M x) then Xf x else A0.

(** Source for [dgpr_main_extension_on]: the extension agrees with X
    on M; proof of blueprint lem:compact_case. *)
Lemma dgpr_main_extension_on (M : set X) (Xf : X -> Hom X Y) (A0 : Hom X Y) (x : X) :
  M x -> dgpr_main_extension M Xf A0 x = Xf x.
Proof. by rewrite /dgpr_main_extension; case: pselect. Qed.
End Extension.

Section MainToStanding.
Variable R : realType.
Variables n k : nat.
Hypothesis hk : (0 < k <= n)%N.
Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Local Notation RnM := (inner_metric_space BX).
Local Notation HK := (@hausdorff_measure R RnM k).
Variable Y : lmodType R.
Variable CY : Y -> Y -> R.
Hypothesis hCY : is_inner_product CY.
Variable d : nat.
Variable eY : 'I_d -> Y.
Hypothesis heY : is_basis eY.
Local Notation NY := (inner_norm hCY).
Local Notation hNY := (inner_norm_real_norm hCY).
Local Notation BH := (hom_inner_productP BX hCY heX).
Local Notation hNH := (inner_norm_real_norm BH).
Local Notation BD := (hom_inner_productP hCY (scalar_inner_productP R) heY).
Local Notation ND := (hom_norm hCY (scalar_inner_productP R) heY).
Local Notation hND := (inner_norm_real_norm BD).
Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space hN hNY setT ev.
Variable K : set (real_norm_metric_space hNH).
Variables lam Lam : R.
Variable M : set RnM.
Variable theta : X -> R.
Variable Xf : X -> Hom X Y.
Variable Ups : Hom (smooth_test_space hE) R^o.
Variable ups : set (real_norm_metric_space hN) -> \bar R.
Hypothesis hH :
  @dgpr_main_hypotheses R n k hk Y CY hCY d eY E ev hE K lam Lam M theta Xf Ups ups.
Local Notation mu := (dgpr_main_measure k M theta).
Variables a r0 : R.
Hypothesis ha : mu setT = a%:E.
Hypothesis ha0 : 0 < a.
Hypothesis hr0 : 0 < r0.
Hypothesis hsupp : measure_almost_everywhere mu [set y | N y <= r0].
Variable A0 : Hom X Y.
Hypothesis hA0 : K A0.
Variable dups : X -> Hom Y R^o.
Hypothesis hdm : is_measure_measurable_function ups
  (partial_function_total (fun z => (dups z : real_norm_metric_space hND))).
Hypothesis hdb : forall z, ND (dups z) <= 1.
Hypothesis hda : forall g : smooth_test_space hE,
  is_measure_integral ups (real_total_integrand (fun z => dups z (smooth_test_value hE g z)))
    (Ups g)%:E.
Local Notation Xe := (dgpr_main_extension M Xf A0).

(** Source for [dgpr_main_standing]: blueprint proof of
    lem:compact_case, first paragraph: for the data of
    mr:hypotheses_main with a = μ(R^n) > 0 and μ(R^n ∖ B(0, r_0)) = 0,
    and a dual density dΥ of ‖Υ‖ as in mr:functionals, the hypotheses
    (S) of mr:standing hold for the normalised data a^{-1} μ, the
    extension of X by A_0 ∈ K, a^{-1} Υ, a^{-1} ‖Υ‖, dΥ,
    δ = a^{-1} ‖Υ‖(R^n), T = 1 and μ_0 = a^{-1} μ with γ = 1. *)
Theorem dgpr_main_standing :
  dgpr_standing heY hk K lam Lam (measure_scale a^-1 mu) r0 Xe (a^-1 *: Ups)
    (measure_scale a^-1 ups) dups (a^-1 * fine (ups setT)) 1 (measure_scale a^-1 mu) 1.
Proof.
have hai : 0 < a^-1 by rewrite invr_gt0.
have htheta := dgpr_main_theta_nonnegative hH.
have hmu : is_measure mu := dgpr_main_measure_is_measure k htheta.
have hmass : measure_scale a^-1 mu setT = 1%:E.
  by rewrite /measure_scale ha -EFinM mulVf ?gt_eqF.
have hups := dgpr_main_ups_measure hH.
have hupsfin : ups setT = (fine (ups setT))%:E.
  by rewrite fineK // ge0_fin_numE ?(measure_nonnegative hups) // (dgpr_main_ups_finite hH).
have hopen : forall A : set (real_norm_metric_space hN), open A ->
    measure_measurable (measure_scale a^-1 mu) A.
  move=> A hA; apply: (measure_scale_measurable hmu); exact (dgpr_main_measure_open k htheta hA).
have hHMm : is_measure (measure_restrict HK M) :=
  measure_restrict_is_measure (hausdorff_measure_is_measure RnM k) M.
have hHMon : measure_almost_everywhere (measure_restrict HK M) M.
  rewrite /measure_almost_everywhere /measure_restrict setICr.
  exact: measure_empty (hausdorff_measure_is_measure RnM k).
constructor.
- exact: dgpr_main_K_nonempty hH.
- exact: dgpr_main_K_compact hH.
- exact: dgpr_main_K_convex hH.
- exact: dgpr_main_lambda hH.
- exact: dgpr_main_Lambda hH.
- exact: dgpr_main_K_sv hH.
- exact: dgpr_main_K_norm hH.
- exact: measure_scale_is_measure hmu hai.
- exact: hopen.
- exact: hmass.
- exact: hr0.
- exact: measure_scale_almost_everywhere hsupp.
- apply: (measure_scale_measurable_function hmu); apply: (dgpr_main_measure_function htheta).
  apply: (measurable_function_almost_equal hHMm (dgpr_main_X_measurable hH)).
  apply: (measure_almost_everywhere_mono hHMm _ hHMon) => x hx.
  by exists (Xf x); split=> //=; rewrite dgpr_main_extension_on.
- move=> y; rewrite /dgpr_main_extension; case: pselect => hy //.
  exact: dgpr_main_X_values hH y hy.
- move=> g Dg hDg.
  have h := dgpr_main_constraint hH hDg.
  have h2 : is_measure_integral mu
      (real_total_integrand (fun x => hom_inner BX hCY heX (Xe x) (Dg x))) (- Ups g)%:E.
    apply: (measure_integral_almost_equal hmu h).
    apply: (measure_almost_everywhere_mono hmu _ (dgpr_main_measure_on k M theta)) => x hx.
    exists (hom_inner BX hCY heX (Xf x) (Dg x))%:E.
    by split; apply/real_total_integrand_graph => //; rewrite dgpr_main_extension_on.
  have h3 := measure_scale_integral hmu hai h2.
  have e : (a^-1%:E * (- Ups g)%:E)%E = (- (a^-1 *: Ups) g)%:E.
    by rewrite -EFinM hom_scaleE mulrN.
  by rewrite -e.
- exact: measure_scale_is_measure hups hai.
- exact (dgpr_measure_scale_radon hups (dgpr_main_ups_radon hH) hai).
- move=> f hf; have [b [hvb hib]] := dgpr_main_ups_gauge hH hf.
  exists (a^-1 * b); rewrite EFinM; split.
  + exact: dgpr_variation_value_scale hai hvb.
  + exact (measure_scale_integral hups hai hib).
- by rewrite /measure_scale hupsfin -EFinM.
- exact (measure_scale_measurable_function hups _ hdm).
- exact: hdb.
- move=> g; have h := measure_scale_integral hups hai (hda g).
  have e : ((a^-1 *: Ups) g)%:E = (a^-1%:E * (Ups g)%:E)%E by rewrite hom_scaleE EFinM.
  by rewrite e.
- exact: ltr01.
- exact: measure_scale_is_measure hmu hai.
- exact: hopen.
- by move=> A.
- exact: hmass.
- exact: ltr01.
Qed.
End MainToStanding.
