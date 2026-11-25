(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    mr:functionals: the variation measure ||S|| and the normalised dual
    density of a distribution S with values in a finite dimensional
    normed space Z which is representable by integration (Federer 4.1.5,
    by 2.5.12 and 2.5.14). The representation is Federer's
    [finite_distribution_radon_representation]; the hypotheses of
    completeness and separability of Z are derived here from a finite
    basis of Z. The file also proves the second consequence of
    mr:functionals at the level of the gauge: ||S||(f) = 0 whenever f
    vanishes on a set on whose complement every test with S(phi) <> 0 is
    supported, and at the level of the measure: ||S||(R^n - C) = 0 for
    the Radon variation measure ||S||, by Federer 2.5.14. The first
    consequence, ||S||(A) <= nu(A) for a Radon measure nu, is proved
    from the gauge bound ||S||(f) <= integral of f with respect to nu for
    f in K(X)^+, and then from S(phi) <= upper integral of |phi| with
    respect to nu by monotonicity of the upper integral (Federer 2.4.2,
    2.4.4). *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP CompleteMetricUP
  ContinuousDualUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  VectorDaniellHypotheses SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation WeakEvaluationTopologyUP
  DistributionVariationDomain DistributionVariationUP DistributionFiniteVariationUP
  NormalisedDistributionRepresentationUP FiniteDistributionRadonRepresentation ExtendedSupremumUP
  LinearBasis FiniteNormMetricPolish MeasureUP MeasureIntegralUP MeasureIntegralUniqueness
  RadonMeasureUP FunctionLatticeUP CompactSupportFunctionUP RealIntegralFunctionalUP
  SummableRealFunctionUP CompactOpenContentUP ExtendedRealBoundsUP RadonPositiveCompactOpenContent
  DistributionIntegrationRepresentationUP CurrentDomain CurrentDomainGeometry MeasureBasic
  ExtendedRealBounds RadonMeasureBounds RadonCompactScalarIntegral MeasureIntegralBounds
  MeasureUpperIntegralMonotone RealTotalCharacteristicBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dgpr_functional_representation]: blueprint
    mr:functionals, first paragraph, with Federer 4.1.5, pp. 349-350: a
    distribution S on an open subset U of R^n with values in a finite
    dimensional normed space Y and with ||S||(f) < infinity for f in
    K(U)^+ has a Radon variation measure rho and a rho measurable dual
    density k with ||k(x)|| = 1 for rho almost all x, such that S is the
    integral of the pairing of the test with k with respect to rho. *)
Theorem dgpr_functional_representation (R : realType) (n : nat)
    (Y : lmodType R) (NY : Y -> R) (hNY : is_real_norm NY)
    d (b : 'I_d -> Y) (hb : is_basis b)
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (E : lmodType R) (ev : E -> R_n R n -> Y)
    (hE : is_smooth_function_space (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY U ev)
    (S : Hom (smooth_test_space hE) R^o)
    (D : lmodType R) (ed : Hom D (Hom Y R^o)) (DN : D -> R) (hD : is_continuous_dual hNY ed DN)
    (O : set (set D)) (hO : is_weak_evaluation_topology (fun a y => ed a y) O) :
  @is_finite_distribution_variation R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    U Y NY (smooth_test_space hE) (smooth_test_values_hom hE) S ->
  exists rho : set (set_type (U : set (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))))) -> \bar R,
  exists k, is_normalised_distribution_representation hD hO
    (@distribution_domain_values R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      U Y (smooth_test_space hE) (smooth_test_values_hom hE)) S rho k.
Proof.
have hY := finite_norm_metric_complete (hN := hNY) hb.
have hSep : is_separable_normed_space hNY := finite_norm_metric_separable hNY hb.
exact: (@finite_distribution_radon_representation R n Y NY hNY hY hSep U hU E ev hE S D ed DN hD O hO).
Qed.

(** Source for [dgpr_variation_vanishes]: blueprint mr:functionals,
    second consequence, first assertion: if S(phi) = 0 for every test
    phi vanishing on G, then ||S||(f) = 0 for every nonnegative f
    vanishing on G, because |phi(x)| <= f(x) for x in X forces phi to
    vanish on G. With G an open neighbourhood of the closed set C, the
    hypothesis is the condition "S(phi) = 0 whenever spt phi and C are
    disjoint" of mr:functionals. *)
Lemma dgpr_variation_vanishes (R : realType) (X : choiceType) (Y : lmodType R) (NY : Y -> R)
    (hNY : is_real_norm NY) (E : lmodType R)
    (value : Hom E (GRing.Lmodule.clone R (X -> Y) _)) (S : Hom E R^o) (G : set X) (f : X -> R) :
  (forall phi, (forall x, G x -> value phi x = 0) -> S phi = 0) ->
  (forall x, 0 <= f x) -> (forall x, G x -> f x = 0) ->
  is_distribution_variation_value NY value S f 0%E.
Proof.
move=> hS hf0 hfG; constructor.
  move=> a [phi [hphi <-]]; rewrite hS //= => x hx.
  apply: hNY.2; apply/eqP; rewrite eq_le real_seminorm_nonnegative ?andbT; last exact: hNY.1.
  by rewrite -(hfG x hx); exact: hphi.
move=> c hc; apply: hc; exists 0; split; last exact: linear0.
by move=> x; rewrite linear0 (real_seminorm_zero hNY.1); exact: hf0.
Qed.

Section Consequences.
Variable R : realType.
Variable X : topologicalType.
Variable Y : lmodType R.
Variable NY : Y -> R.
Hypothesis hNY : is_real_norm NY.
Variable E : lmodType R.
Variable value : Hom E (GRing.Lmodule.clone R (X -> Y) _).
Variable S : Hom E R^o.
Variable rho : set X -> \bar R.
Hypothesis hm : is_measure rho.
Hypothesis hr : is_radon_measure rho.
Hypothesis hX : locally_compact [set: X].
Hypothesis hgauge : forall f,
  positive_function_lattice (@compactly_supported_continuous_functions R X) f ->
  exists b : R, is_distribution_variation_value NY value S f b%:E /\
    is_measure_integral rho (real_total_integrand f) b%:E.

(** Source for [dgpr_variation_null_outside]: blueprint mr:functionals,
    second consequence: if C is a closed subset of X and S(phi) = 0
    whenever phi vanishes on an open set containing C (that is, whenever
    spt phi and C are disjoint), then ||S||(X - C) = 0. The Radon
    measure rho represents the gauge ||S|| on K(X)^+, and its value on
    the open set X - C is the supremum of ||S||(f) over the tests
    0 <= f <= 1 with spt f contained in X - C (Federer 2.5.14, p. 107);
    each of these values vanishes by [dgpr_variation_vanishes]. *)
Theorem dgpr_variation_null_outside (C : set X) :
  closed C ->
  (forall phi (G : set X), open G -> C `<=` G -> (forall x, G x -> value phi x = 0) -> S phi = 0) ->
  rho (~` C) = 0%E.
Proof.
move=> hC hS.
pose F (f : X -> R) : R := xget 0 [set b : R | is_measure_integral rho (real_total_integrand f) b%:E].
have hF : is_real_integral_functional rho
    (positive_function_lattice (@compactly_supported_continuous_functions R X)) F.
  move=> f hf; have [b [_ hb]] := hgauge hf.
  exact: (@xgetPex R 0 [set b : R | is_measure_integral rho (real_total_integrand f) b%:E]
    (ex_intro _ b hb)).
have hc := radon_positive_compact_open_content hm hr hX hF.
have hV : open (~` C) by rewrite openC.
have [_ hleast] := hc (~` C) hV.
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT; apply: hleast.
move=> c [f [[hfK [hf01 hspt]] ->]].
have hf0 x : 0 <= f x by have /andP[] := hf01 x.
have hfp : positive_function_lattice (@compactly_supported_continuous_functions R X) f.
  by split=> // x; exact: hf0.
have [b [hgb hib]] := hgauge hfp.
have hFb : F f = b by case: (measure_integral_unique (hF f hfp) hib).
have hzero : is_distribution_variation_value NY value S f 0%E.
  apply: (@dgpr_variation_vanishes R X Y NY hNY E value S (~` real_function_support f)).
  - move=> phi hphi; apply: (hS phi (~` real_function_support f)) => //.
      by rewrite openC; exact: real_function_support_closed.
    by move=> x hx hsx; exact: (hspt x hsx).
  - exact: hf0.
  - move=> x hx; apply/eqP/negPn/negP => hfx; apply: hx; apply: subset_closure.
    by move/eqP: hfx.
have [hb0] := distribution_variation_value_unique hgb hzero.
by rewrite hFb hb0.
Qed.

Variable nu : set X -> \bar R.
Hypothesis hn : is_measure nu.
Hypothesis hnr : is_radon_measure nu.

(** Source for [dgpr_variation_dominated]: blueprint mr:functionals,
    first consequence: if ||S||(f) <= integral of f with respect to the
    Radon measure nu for every f in K(X)^+, that is, if
    S(phi) <= integral of f with respect to nu whenever |phi(x)| <= f(x)
    for x in X, then ||S||(A) <= nu(A) for every A contained in X. Both
    measures are Radon measures; their values on open sets are suprema
    over the same tests (Federer 2.5.14, p. 107), and both are outer
    regular (Federer 2.2.5, p. 62). *)
Theorem dgpr_variation_dominated :
  (forall f, positive_function_lattice (@compactly_supported_continuous_functions R X) f ->
    forall b : R, is_measure_integral nu (real_total_integrand f) b%:E ->
    forall phi, (forall x, NY (value phi x) <= f x) -> S phi <= b) ->
  forall A, (rho A <= nu A)%E.
Proof.
move=> hdom.
pose F (f : X -> R) : R := xget 0 [set b : R | is_measure_integral rho (real_total_integrand f) b%:E].
have hF : is_real_integral_functional rho
    (positive_function_lattice (@compactly_supported_continuous_functions R X)) F.
  move=> f hf; have [b [_ hb]] := hgauge hf.
  exact: (@xgetPex R 0 [set b : R | is_measure_integral rho (real_total_integrand f) b%:E]
    (ex_intro _ b hb)).
pose Fn := radon_positive_compact_integral hn hnr.
have hFn := radon_positive_compact_integral_laws hn hnr.
have hc := radon_positive_compact_open_content hm hr hX hF.
have hcn := radon_positive_compact_open_content hn hnr hX hFn.
have hopen V : open V -> (rho V <= nu V)%E.
  move=> hV; have [_ hleast] := hc V hV; have [hupper _] := hcn V hV.
  apply: hleast => c [f [hfV ->]].
  have hf0 x : 0 <= f x by have /andP[] := hfV.2.1 x.
  have hfp : positive_function_lattice (@compactly_supported_continuous_functions R X) f.
    by split; [exact: hfV.1|move=> x; exact: hf0].
  have [b [hgb hib]] := hgauge hfp.
  have hFb : F f = b by case: (measure_integral_unique (hF f hfp) hib).
  rewrite hFb; apply: le_trans (hupper (Fn f)%:E _); last by exists f.
  apply: (extended_supremum_least hgb) => a [phi [hphi <-]].
  by rewrite lee_fin; exact: hdom hfp (Fn f) (hFn f hfp) phi hphi.
move=> A; rewrite (radon_outer_formula hn hnr A).
apply: extended_real_inf_greatest => t [V [hV [hAV ->]]].
exact: le_trans (measure_mono hm hAV) (hopen V hV).
Qed.

(** Source for [dgpr_variation_dominated_integral]: blueprint
    mr:functionals, first consequence, in the stated form: if
    S(phi) <= integral of |phi| with respect to the Radon measure nu for
    every test phi (the upper integral of Federer 2.4.2, p. 81, which is
    the integral whenever |phi| is nu summable), then ||S||(A) <= nu(A)
    for every A contained in X; indeed ||S||(f) <= integral of f with
    respect to nu for f in K(X)^+ by Federer 2.4.4, p. 82. *)
Theorem dgpr_variation_dominated_integral :
  (forall phi, ((S phi)%:E <=
    measure_upper_integral nu (real_total_integrand (fun x => NY (value phi x))))%E) ->
  forall A, (rho A <= nu A)%E.
Proof.
move=> hS; apply: dgpr_variation_dominated => f hf b hb phi hphi.
have hmono := measure_upper_integral_monotone hn (real_total_pointwise_order_almost hn hphi).
have hfb : measure_upper_integral nu (real_total_integrand f) = b%:E.
  exact: measure_upper_integral_unique (measure_upper_integral_specification nu _) hb.2.1.
by rewrite -lee_fin; apply: le_trans (hS phi) _; rewrite -hfb.
Qed.
End Consequences.

(** Source for [dgpr_functional_null_outside]: blueprint
    mr:functionals, second consequence, for a distribution S on an open
    subset U of R^n with its normalised representation of Federer 4.1.5:
    if C is closed in U and S(phi) = 0 whenever phi vanishes on an open
    set containing C, then ||S||(U - C) = 0. *)
Theorem dgpr_functional_null_outside (R : realType) (n : nat)
    (Y : lmodType R) (NY : Y -> R) (hNY : is_real_norm NY)
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (E : lmodType R) (value : Hom E (GRing.Lmodule.clone R (current_domain R n U -> Y) _))
    (S : Hom E R^o)
    (D : lmodType R) (ed : Hom D (Hom Y R^o)) (DN : D -> R) (hD : is_continuous_dual hNY ed DN)
    (O : set (set D)) (hO : is_weak_evaluation_topology (fun a y => ed a y) O)
    (rho : set (current_domain R n U) -> \bar R) (k : current_domain R n U -> D)
    (C : set (current_domain R n U)) :
  is_normalised_distribution_representation hD hO value S rho k ->
  closed C ->
  (forall phi (G : set (current_domain R n U)), open G -> C `<=` G ->
    (forall x, G x -> value phi x = 0) -> S phi = 0) ->
  rho (~` C) = 0%E.
Proof.
move=> hrep; have hlaws := normalised_distribution_representation_laws hrep.
apply: (@dgpr_variation_null_outside R (current_domain R n U) Y NY hNY E value S rho
  (distribution_representation_measure hlaws) (distribution_representation_radon hlaws)
  (current_domain_locally_compact hU) (normalised_distribution_original_gauge hrep)).
Qed.
