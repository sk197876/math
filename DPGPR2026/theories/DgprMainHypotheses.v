(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    mr:hypotheses_main and the statement of thm:main (Theorem 1.1 of
    DPGPR 2026 for rectifiable data). This file fixes the interface
    against which thm:main is to be proved and from which thm:MS is
    deduced (DgprMichaelSimon.v). It contains no proof of thm:main.

    The data of mr:hypotheses_main are parameters of the predicate
    [dgpr_main_hypotheses]: the dimensions n, k with 1 <= k <= n; a finite
    dimensional inner product space Y (inner product CY, basis eY); a
    realisation E of the space of smooth maps R^n -> Y (Federer 4.1.1),
    whose test space D(R^n, Y) is [smooth_test_space hE]; the set
    K ⊆ Hom(R^n, Y); the numbers λ and Λ; the set M ⊆ R^n; the density
    θ : R^n -> R, whose values off M play no role; the map X : R^n -> Hom(R^n, Y),
    whose values off M play no role; the distribution Υ ∈ D'(R^n, Y); and
    its variation measure ‖Υ‖ (mr:functionals).

    The measure μ = (H^k ⌞ M) ⌞ θ of Federer 2.4.10 is the explicit
    formula [dgpr_main_measure M θ], as in DgprInnerApproximation.v. The
    functional σ(Φ) = ∫ X • Φ dμ is not a separate object: the relation
    Υ(g) = −σ(Dg) is the assertion that [x ↦ X(x) • Dg(x)] is μ summable
    with integral −Υ(g), for every g ∈ D(R^n, Y) and its differentials
    Dg(x), as in DgprStanding.v. The condition “Υ is representable by
    integration and ‖Υ‖(R^n) < ∞” is expressed through a Radon measure
    ‖Υ‖ over R^n which represents the variation ‖Υ‖(f) of Federer 4.1.5
    on the nonnegative continuous functions f with compact support, and
    which satisfies ‖Υ‖(R^n) < ∞; such a measure is unique
    ([dgpr_variation_measure_unique]), and its existence implies that Υ
    is representable by integration. Hom(R^n, Y) carries the inner
    product A • B = trace(A^* ∘ B) and the norm |A| of Federer 1.7.9.

    The conclusion of thm:main for given λ, Λ and C is the proposition
    [dgpr_main_inequality n k hk λ Λ C]: for every Y and all data
    satisfying [dgpr_main_hypotheses],
        μ(R^n) ≤ C H^k(M)^{1/k} ‖Υ‖(R^n)
    in the extended real numbers, with H^k(M)^{1/k} the real power of
    the finite number H^k(M). *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LinearBasis HomInner InnerConvex
  InnerMetric PartialFunctionUP PartialFunctionBasic MeasureUP MeasureRestriction MeasureDensity
  MeasurableFunctionUP MeasureIntegralUP SummableRealFunctionUP RadonMeasureUP FunctionLatticeUP
  CompactSupportFunctionUP DistributionVariationUP SmoothFunctionSpaceUP SmoothTestSpaces
  SmoothTestEvaluation NormDifferentialUP HausdorffMeasure RectifiableSetUP TopologicalBorel
  RealPower ExtendedSupremumUP MeasureIntegralUniqueness.
From DPGPR Require Import DgprSingularValue DgprFunctionals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section MainHypotheses.
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
Local Notation NY := (inner_norm hCY).
Local Notation hNY := (inner_norm_real_norm hCY).
Local Notation BH := (hom_inner_productP BX hCY heX).
Local Notation NH := (hom_norm BX hCY heX).
Local Notation hNH := (inner_norm_real_norm BH).
Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space hN hNY setT ev.

(** Source for [dgpr_main_measure]: blueprint mr:hypotheses_main, the
    measure μ = (H^k ⌞ M) ⌞ θ of Federer 2.4.10, p. 85; the values of θ
    off M do not matter. Definition. *)
Definition dgpr_main_measure (M : set RnM) (theta : X -> R) : set RnM -> \bar R :=
  measure_with_density (measure_restrict HK M) (real_total_integrand theta).

(** Source for [dgpr_main_hypotheses]: blueprint mr:hypotheses_main.
    The family eY is a basis of Y, so that Y is finite dimensional.
    K is a nonempty compact convex subset of Hom(R^n, Y) with
    sv_k(A) ≥ λ and |A| ≤ Λ for A ∈ K (def:sv); 0 < λ and 0 < Λ; M is a
    Borel set which is countably (H^k, k) rectifiable (Federer 3.2.14)
    with H^k(M) < ∞; θ is nonnegative on M and H^k ⌞ M summable; X maps
    M into K and is H^k ⌞ M measurable; Υ(g) = −σ(Dg) = −∫ X • Dg dμ for
    every g ∈ D(R^n, Y) and its differentials Dg; ‖Υ‖ is a Radon measure
    over R^n representing the variation of Υ (Federer 4.1.5,
    mr:functionals) with ‖Υ‖(R^n) < ∞. Definition. *)
Record dgpr_main_hypotheses (K : set (real_norm_metric_space hNH)) (lam Lam : R)
    (M : set RnM) (theta : X -> R) (Xf : X -> Hom X Y)
    (Ups : Hom (smooth_test_space hE) R^o) (ups : set (real_norm_metric_space hN) -> \bar R) :
    Prop := {
  dgpr_main_Y_basis : is_basis eY;
  dgpr_main_K_nonempty : exists A, K A;
  dgpr_main_K_compact : compact K;
  dgpr_main_K_convex : is_inner_convex K;
  dgpr_main_lambda : 0 < lam;
  dgpr_main_Lambda : 0 < Lam;
  dgpr_main_K_sv : forall A, K A -> lam <= dgpr_sv BX hCY heX hk A;
  dgpr_main_K_norm : forall A, K A -> NH A <= Lam;
  dgpr_main_M_borel : borel_set M;
  dgpr_main_M_rectifiable : is_countably_measure_m_rectifiable HK k M;
  dgpr_main_M_finite : (HK M < +oo)%E;
  dgpr_main_theta_nonnegative : forall x, M x -> 0 <= theta x;
  dgpr_main_theta_summable : summable_real_functions (measure_restrict HK M) theta;
  dgpr_main_X_values : forall x, M x -> K (Xf x);
  dgpr_main_X_measurable : is_measure_measurable_function (measure_restrict HK M)
    (partial_function_total (fun x => (Xf x : real_norm_metric_space hNH)));
  dgpr_main_constraint : forall (g : smooth_test_space hE) (Dg : X -> Hom X Y),
    (forall x, has_norm_differential N NY setT (smooth_test_value hE g) x (Dg x)) ->
    is_measure_integral (dgpr_main_measure M theta)
      (real_total_integrand (fun x => hom_inner BX hCY heX (Xf x) (Dg x))) (- Ups g)%:E;
  dgpr_main_ups_measure : is_measure ups;
  dgpr_main_ups_radon : is_radon_measure ups;
  dgpr_main_ups_gauge : forall f,
    positive_function_lattice (@compactly_supported_continuous_functions R (real_norm_metric_space hN)) f ->
    exists b : R, is_distribution_variation_value NY (smooth_test_values_hom hE) Ups f b%:E /\
      is_measure_integral ups (real_total_integrand f) b%:E;
  dgpr_main_ups_finite : (ups setT < +oo)%E
}.

End MainHypotheses.

Section MainInequality.
Variable R : realType.
Variables n k : nat.
Hypothesis hk : (0 < k <= n)%N.
Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation RnM := (inner_metric_space BX).
Local Notation HK := (@hausdorff_measure R RnM k).

(** Source for [dgpr_main_inequality]: blueprint thm:main, the
    conclusion for the numbers λ, Λ and C: whenever Y is a finite
    dimensional inner product space and the data of mr:hypotheses_main
    are given with these λ and Λ, then
    μ(R^n) ≤ C H^k(M)^{1/k} ‖Υ‖(R^n). Theorem 1.1 of DPGPR 2026 for
    rectifiable data asserts that for 0 < λ and 0 < Λ some 0 < C < ∞
    has this property. Definition. *)
Definition dgpr_main_inequality (lam Lam C : R) : Prop :=
  forall (Y : lmodType R) (CY : Y -> Y -> R) (hCY : is_inner_product CY)
    (d : nat) (eY : 'I_d -> Y) (E : lmodType R) (ev : E -> X -> Y) (hE : is_smooth_function_space hN (inner_norm_real_norm hCY) setT ev)
    K M (theta : X -> R) (Xf : X -> Hom X Y) (Ups : Hom (smooth_test_space hE) R^o)
    (ups : set (real_norm_metric_space hN) -> \bar R),
  @dgpr_main_hypotheses R n k hk Y CY hCY d eY E ev hE K lam Lam M theta Xf Ups ups ->
  (dgpr_main_measure k M theta setT <=
    (C * real_power (fine (HK M)) (k%:R)^-1)%:E * ups setT)%E.

End MainInequality.

Section VariationMeasure.
Variable R : realType.
Variable T : topologicalType.
Variable Y : lmodType R.
Variable NY : Y -> R.
Hypothesis hNY : is_real_norm NY.
Variable E : lmodType R.
Variable value : Hom E (GRing.Lmodule.clone R (T -> Y) _).
Variable S : Hom E R^o.
Hypothesis hT : locally_compact [set: T].

(** Source for [dgpr_variation_measure_unique]: blueprint mr:functionals,
    with Federer 2.5.14, p. 107: two Radon measures over a locally
    compact space whose integrals of every nonnegative continuous
    function with compact support are the variation ‖S‖(f) of Federer
    4.1.5 agree on all sets. Hence the measure ‖Υ‖ of
    [dgpr_main_hypotheses] is the variation measure of Υ. *)
Theorem dgpr_variation_measure_unique (rho nu : set T -> \bar R) :
  is_measure rho -> is_radon_measure rho -> is_measure nu -> is_radon_measure nu ->
  (forall f, positive_function_lattice (@compactly_supported_continuous_functions R T) f ->
    exists b : R, is_distribution_variation_value NY value S f b%:E /\
      is_measure_integral rho (real_total_integrand f) b%:E) ->
  (forall f, positive_function_lattice (@compactly_supported_continuous_functions R T) f ->
    exists b : R, is_distribution_variation_value NY value S f b%:E /\
      is_measure_integral nu (real_total_integrand f) b%:E) ->
  rho = nu.
Proof.
move=> hm hr hn hnr hgr hgn.
have hdom (mu1 mu2 : set T -> \bar R) : is_measure mu1 -> is_radon_measure mu1 ->
    is_measure mu2 -> is_radon_measure mu2 ->
    (forall f, positive_function_lattice (@compactly_supported_continuous_functions R T) f ->
      exists b : R, is_distribution_variation_value NY value S f b%:E /\
        is_measure_integral mu1 (real_total_integrand f) b%:E) ->
    (forall f, positive_function_lattice (@compactly_supported_continuous_functions R T) f ->
      exists b : R, is_distribution_variation_value NY value S f b%:E /\
        is_measure_integral mu2 (real_total_integrand f) b%:E) ->
    forall A, (mu1 A <= mu2 A)%E.
  move=> h1 h1r h2 h2r hg1 hg2.
  apply: (@dgpr_variation_dominated R T Y NY E value S mu1 h1 h1r hT hg1 mu2 h2 h2r).
  move=> f hf b hb phi hphi.
  have [c [hc hci]] := hg2 f hf.
  have [hcb] := measure_integral_unique hci hb.
  rewrite -hcb -lee_fin.
  by apply: (extended_supremum_upper hc); exists phi.
apply: funext => A; apply/eqP; rewrite eq_le.
by rewrite (hdom rho nu) // (hdom nu rho).
Qed.

End VariationMeasure.
