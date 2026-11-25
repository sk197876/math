(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    mr:functionals, first consequence, in the form used in the proof of
    thm:main: a distribution S ∈ D'(R^n, Y), Y finite dimensional, with
    S(φ) ≤ m B whenever |φ(x)| ≤ m for x ∈ R^n, is representable by
    integration, and its variation measure ‖S‖ is a Radon measure over
    R^n with ‖S‖(R^n) ≤ B. The variation measure of Federer 4.1.5 lives
    on the current domain of R^n ([dgpr_functional_representation]); it
    is carried to R^n by the canonical inclusion, as in Federer's
    [current_ambient_variation]. Conversely, if ‖Υ‖ is a Radon measure
    representing the variation of Υ with ‖Υ‖(R^n) < ∞, then
    Υ(φ) ≤ m ‖Υ‖(R^n) whenever |φ(x)| ≤ m for x ∈ R^n. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP RealSeminormDifference NormMetric NormDifferentialUP
  NormOpenDomainLaws NormClassOneUP NormRegularity NormClassZeroTopology InnerNorm InnerMetric
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LinearBasis CurrentDomain
  CurrentDomainGeometry IsotropyGroupTopology ProperMapUP RadonProperPushforward FiniteNormEquivalence
  EuclideanFullDomainMeasure EuclideanFullDomainCompactFunctions MeasureUP MeasurePushforward
  RadonMeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralComparison MeasureIntegralGraphEquivalence RealTotalCharacteristicBounds
  FiniteMeasureBoundedNorm RadonWeightedPushforwardIntegral PartialFunctionUP PartialFunctionBasic
  MeasureAlmostUP MeasureAlmostBasic SummableRealFunctionUP FunctionLatticeUP CompactSupportFunctionUP
  CompactOpenContentUP RadonPositiveCompactOpenContent RealIntegralFunctionalUP ContinuousDualUP
  ContinuousDualSealed WeakEvaluationTopologyUP WeakEvaluationTopologySealed SmoothFunctionSpaceUP
  SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation DistributionVariationDomain
  DistributionVariationUP DistributionVariationSealed DistributionFiniteVariationUP
  NormalisedDistributionRepresentationUP DistributionIntegrationRepresentationUP ExtendedSupremumUP
  ExtendedRealBoundsUP CompactMaximum RealMetricBackground.
From DPGPR Require Import DgprFunctionals DgprMichaelSimon.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dgpr_compact_function_bounded]: Federer 2.5.13,
    p. 106: a nonnegative continuous function f with compact support is
    bounded; it attains its maximum on spt f (Federer 2.1.7) and
    vanishes outside spt f. Supporting lemma. *)
Lemma dgpr_compact_function_bounded (R : realType) (T : topologicalType) (f : T -> R) :
  positive_function_lattice (@compactly_supported_continuous_functions R T) f ->
  exists m : R, forall x, f x <= m.
Proof.
move=> [[hc hK] hf0].
have hzero x : ~ real_function_support f x -> f x = 0.
  move=> hx; apply: contrapT => hne; apply: hx; exact: subset_closure.
have [hne|hempty] := pselect (real_function_support f !=set0).
- have hc' : continuous (f : T -> R^o) := hc.
  have [c [_ hmax]] := continuous_compact_maximum hne hK hc'.
  exists (f c) => x.
  have [hx|hx] := pselect (real_function_support f x); first exact: hmax.
  by rewrite (hzero x hx); exact: hf0.
- exists 0 => x; rewrite hzero //; move=> hx; apply: hempty; by exists x.
Qed.

Section VariationMass.
Variable R : realType.
Variable T : topologicalType.
Variable Y : lmodType R.
Variable NY : Y -> R.
Variable E : lmodType R.
Variable value : Hom E (GRing.Lmodule.clone R (T -> Y) _).
Variable S : Hom E R^o.
Variable rho : set T -> \bar R.
Hypothesis hm : is_measure rho.
Hypothesis hr : is_radon_measure rho.
Hypothesis hT : locally_compact [set: T].
Hypothesis hgauge : forall f,
  positive_function_lattice (@compactly_supported_continuous_functions R T) f ->
  exists b : R, is_distribution_variation_value NY value S f b%:E /\
    is_measure_integral rho (real_total_integrand f) b%:E.

(** Source for [dgpr_variation_mass_bound]: blueprint mr:functionals,
    with Federer 2.5.14, p. 107: the value of the Radon measure ‖S‖ on
    the open set T is the supremum of ‖S‖(f) over the tests f with
    0 ≤ f ≤ 1; hence ‖S‖(T) ≤ B whenever S(φ) ≤ B for every φ with
    |φ(x)| ≤ f(x) ≤ 1 for x ∈ T. Supporting lemma. *)
Lemma dgpr_variation_mass_bound (B : R) :
  (forall (phi : E) (f : T -> R),
    positive_function_lattice (@compactly_supported_continuous_functions R T) f ->
    (forall x, f x <= 1) -> (forall x, NY (value phi x) <= f x) -> S phi <= B) ->
  (rho setT <= B%:E)%E.
Proof.
move=> hB.
pose F (f : T -> R) : R := xget 0 [set b : R | is_measure_integral rho (real_total_integrand f) b%:E].
have hF : is_real_integral_functional rho
    (positive_function_lattice (@compactly_supported_continuous_functions R T)) F.
  move=> f hf; have [b [_ hb]] := hgauge hf.
  exact: (@xgetPex R 0 [set b : R | is_measure_integral rho (real_total_integrand f) b%:E]
    (ex_intro _ b hb)).
have hc := radon_positive_compact_open_content hm hr hT hF.
have [_ hleast] := hc setT openT.
apply: hleast => c [f [[hfK [hf01 _]] ->]].
have hf0 x : 0 <= f x by have /andP[] := hf01 x.
have hf1 x : f x <= 1 by have /andP[] := hf01 x.
have hfp : positive_function_lattice (@compactly_supported_continuous_functions R T) f.
  by split=> // x; exact: hf0.
have [b [hgb hib]] := hgauge hfp.
have hFb : F f = b by case: (measure_integral_unique (hF f hfp) hib).
rewrite hFb; apply: (extended_supremum_least hgb) => a [phi [hphi <-]].
rewrite lee_fin; exact: hB phi f hfp hf1 hphi.
Qed.

End VariationMass.

Section BoundedVariation.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NT := (real_norm_metric_space hN).
Local Notation FT := (current_domain R n (fun _ : X => True)).
Local Notation point := (@euclidean_full_domain_point R n).
Variable Y : lmodType R.
Variable NY : Y -> R.
Hypothesis hNY : is_real_norm NY.
Variable d : nat.
Variable bY : 'I_d -> Y.
Hypothesis hbY : is_basis bY.
Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space hN hNY setT ev.
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R NT setT Y (smooth_test_space hE) values).
Variable S : Hom (smooth_test_space hE) R^o.
Variable B : R.
Hypothesis hS : forall (phi : smooth_test_space hE) (m : R),
  (forall x, NY (smooth_test_value hE phi x) <= m) -> S phi <= m * B.

(** Source for [dgpr_bounded_finite_variation]: blueprint
    mr:functionals: under the hypothesis on S, ‖S‖(f) ≤ m B < ∞ for
    f ∈ K(R^n)^+ with f ≤ m, so S is representable by integration
    (Federer 4.1.5, p. 349). Supporting lemma. *)
Lemma dgpr_bounded_finite_variation :
  @is_finite_distribution_variation R NT setT Y NY (smooth_test_space hE) values S.
Proof.
apply: (proj2 (@finite_distribution_variation_gauge_iff R NT setT Y NY hNY
  (smooth_test_space hE) values S)) => f hf.
have [m hm] := dgpr_compact_function_bounded hf.
have hgauge := @DistributionVariation.laws R FT Y NY hNY (smooth_test_space hE) dvalues S f hf.2.
apply: le_lt_trans (ltry (m * B)).
apply: (extended_supremum_least hgauge) => a [phi [hphi <-]].
rewrite lee_fin; apply: hS => y.
apply: le_trans (hphi (point y)) (hm (point y)).
Qed.

(** Source for [dgpr_bounded_variation_measure]: blueprint
    mr:functionals, first consequence, with Federer 4.1.5, pp. 349–350,
    and 2.5.14, p. 107: there is a Radon measure ‖S‖ over R^n which
    represents the variation of S on K(R^n)^+ and satisfies
    ‖S‖(R^n) ≤ B. Direct formalisation. *)
Theorem dgpr_bounded_variation_measure :
  exists ups : set NT -> \bar R,
    [/\ is_measure ups, is_radon_measure ups,
      (forall f, positive_function_lattice (@compactly_supported_continuous_functions R NT) f ->
        exists b : R, is_distribution_variation_value NY values S f b%:E /\
          is_measure_integral ups (real_total_integrand f) b%:E) &
      (ups setT <= B%:E)%E].
Proof.
have hU : forall x : X, setT x -> norm_domain_interior N setT x.
  move=> x _; exact: norm_full_domain_interior.
have hD := ContinuousDual.laws hNY.
have hO := @WeakEvaluationTopology.laws R Y _ (fun a y => ContinuousDual.evaluation hNY a y).
have [rho [k hrep]] := @dgpr_functional_representation R n Y NY hNY d bY hbY setT hU E ev hE S
  _ _ _ hD _ hO dgpr_bounded_finite_variation.
have hlaws := normalised_distribution_representation_laws hrep.
have hm := distribution_representation_measure hlaws.
have hr := distribution_representation_radon hlaws.
pose ups := measure_pushforward (set_val : FT -> NT) rho.
have hProper : @is_proper_map FT NT set_val.
  move=> K hK.
  have hCompact : compact (point @` K).
    apply: continuous_compact hK.
    exact: continuous_subspaceT (@euclidean_full_domain_point_continuous R n).
  have hEqual : (point @` K) = (set_val @^-1` K : set FT).
    apply: funext => x; apply: propext; split.
    - by move=> [y hy <-].
    - move=> hx; exists (set_val x); first exact: hx.
      apply: val_inj; reflexivity.
  by rewrite -hEqual.
have hLC := @finite_norm_locally_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN.
have hum : is_measure ups by exact: measure_pushforward_is_measure hm.
have hur : is_radon_measure ups.
  exact: (@proper_continuous_radon_pushforward R FT NT rho hm hr set_val
    (@metric_hausdorff R NT) hLC (@set_type_val_continuous NT (fun _ => True)) hProper).
have hgauge : forall f, positive_function_lattice (@compactly_supported_continuous_functions R NT) f ->
    exists b : R, is_distribution_variation_value NY values S f b%:E /\
      is_measure_integral ups (real_total_integrand f) b%:E.
  move=> f hf.
  have hFullF : positive_function_lattice (@compactly_supported_continuous_functions R FT)
      (fun x : FT => f (set_val x)).
    split; first exact: euclidean_full_compact_function_pullback hf.1.
    by move=> x; exact: hf.2 (set_val x).
  have [b [hGauge hIntegral]] := normalised_distribution_original_gauge hrep hFullF.
  have hValues : distribution_variation_values NY dvalues S (fun x : FT => f (set_val x)) =
      distribution_variation_values NY values S f.
    apply: funext => a; apply: propext; split.
    - move=> [omega [hOmega hValue]]; exists omega; split=> // x.
      exact: hOmega (point x).
    - move=> [omega [hOmega hValue]]; exists omega; split=> // x.
      exact: hOmega (set_val x).
  rewrite /is_distribution_variation_value hValues in hGauge.
  exists b; split=> //.
  exact: (@real_total_pushforward_integral_iff R FT NT rho hm (set_val : FT -> NT) f
    hIntegral.1 b%:E).1 hIntegral.
exists ups; split=> //.
apply: (@dgpr_variation_mass_bound R NT Y NY _ values S ups hum hur hLC hgauge B).
move=> phi f hf hf1 hphi.
rewrite -[B]mul1r; apply: hS => y; exact: le_trans (hphi y) (hf1 y).
Qed.

End BoundedVariation.

Section TestBound.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NT := (real_norm_metric_space hN).
Variable Y : lmodType R.
Variable NY : Y -> R.
Hypothesis hNY : is_real_norm NY.
Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space hN hNY setT ev.
Local Notation values := (smooth_test_values_hom hE).
Variable S : Hom (smooth_test_space hE) R^o.
Variable ups : set NT -> \bar R.
Hypothesis hum : is_measure ups.
Hypothesis hgauge : forall f,
  positive_function_lattice (@compactly_supported_continuous_functions R NT) f ->
  exists b : R, is_distribution_variation_value NY values S f b%:E /\
    is_measure_integral ups (real_total_integrand f) b%:E.
Hypothesis hupsf : (ups setT < +oo)%E.

(** Source for [dgpr_test_norm_compact]: Federer 4.1.1, p. 345: for
    φ ∈ D(R^n, Y) the function [x ↦ |φ(x)|] belongs to K(R^n)^+, since
    φ is continuous and spt |φ| = spt φ is compact. Supporting lemma. *)
Lemma dgpr_test_norm_compact (phi : smooth_test_space hE) :
  positive_function_lattice (@compactly_supported_continuous_functions R NT)
    (fun x => NY (smooth_test_value hE phi x)).
Proof.
pose g := smooth_test_value hE phi.
have [D0 hD0] := (norm_class_firstP hN hNY setT g).1 (smooth_test_value_smooth hE phi 1%N).
have hg0 := norm_class_one_zero hD0.
have hz : norm_class_zero N (fun t : R^o => `|t|) setT (fun x => NY (g x)).
  move=> a ha; split; first exact: (hg0 a ha).1.
  move=> e he; have [r [hr hb]] := (hg0 a ha).2 e he.
  exists r; split=> // h hh hhr.
  apply: le_lt_trans (real_seminorm_absolute_difference hNY.1 _ _) _.
  exact: hb h hh hhr.
have hc : continuous (fun x : NT => (NY (g x) : real_line_metric R)).
  apply: dgpr_real_norm_line_continuous => x.
  exact: (@norm_class_zero_continuous_at R X R^o N (fun t : R^o => `|t|) hN
    (@scalar_absolute_value_norm R) setT _ x hz (Logic.I : setT x)).
split; last by move=> x; exact: real_seminorm_nonnegative hNY.1 _.
split; first exact: hc.
have hK := smooth_test_support_compact hE phi.
have -> : real_function_support (fun x : NT => NY (g x)) =
    [set x : NT | @smooth_function_support R X Y N hN setT (smooth_test_space hE)
      (smooth_test_value hE) phi x].
  have hset : [set y : NT | NY (g y) <> 0] = [set y : NT | smooth_test_value hE phi y <> 0].
    apply/seteqP; split=> y hy.
    + by move=> h0; apply: hy; rewrite /g h0 (real_seminorm_zero hNY.1).
    + by move=> h0; apply: hy; exact: hNY.2 _ h0.
  rewrite /real_function_support hset.
  apply/seteqP; split=> x; first by move=> hx; split.
  by move=> [_ hx].
exact: hK.
Qed.

(** Source for [dgpr_test_variation_bound]: blueprint proof of
    thm:main: if |φ(x)| ≤ m for x ∈ R^n, then
    Υ(φ) ≤ ‖Υ‖(|φ|) = ∫ |φ| d‖Υ‖ ≤ m ‖Υ‖(R^n) (Federer 4.1.5, p. 349,
    and 2.4.4, p. 82). Supporting lemma. *)
Lemma dgpr_test_variation_bound (phi : smooth_test_space hE) (m : R) :
  (forall x, NY (smooth_test_value hE phi x) <= m) -> S phi <= m * fine (ups setT).
Proof.
move=> hphi.
have hf := dgpr_test_norm_compact phi.
have [b [hb hib]] := hgauge hf.
have h1 : S phi <= b.
  rewrite -lee_fin; apply: (extended_supremum_upper hb); exists phi; split=> //.
have hups0 : (0 <= ups setT)%E := measure_nonnegative hum setT.
have hfin : ups setT = (fine (ups setT))%:E by rewrite fineK // ge0_fin_numE.
have hc := finite_measure_constant_integral hum m hfin.
have hc' : is_measure_integral ups (real_total_integrand (fun _ : NT => m)) (m * fine (ups setT))%:E.
  apply: (measure_integral_graph_equivalent _ hc) => x y.
  by rewrite real_total_integrand_graph; split => h.
have h2 := measure_integral_monotone hum hib hc'
  (real_total_pointwise_order_almost hum (fun x => hphi x)).
by apply: le_trans h1 _; rewrite -lee_fin.
Qed.

End TestBound.
