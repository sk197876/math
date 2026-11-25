(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    mr:functionals, first paragraph, in the form required by the
    hypotheses (S) of mr:standing: the dual density dΥ of a distribution
    Υ ∈ D'(R^n, Y) with values in a finite dimensional inner product
    space Y, for the Radon measure ‖Υ‖ given in mr:hypotheses_main.

    Suppose ‖Υ‖ is a Radon measure over R^n whose integral of every
    f ∈ K(R^n)^+ is the variation ‖Υ‖(f) of Federer 4.1.5. Then there is
    a map dΥ : R^n → Hom(Y, R) such that dΥ is ‖Υ‖ measurable as a map
    into Hom(Y, R) with the norm of Federer 1.7.9, ‖dΥ(z)‖ ≤ 1 for every
    z ∈ R^n, and
        Υ(g) = ∫ ⟨g(z), dΥ(z)⟩ d‖Υ‖ z     for g ∈ D(R^n, Y)
    ([dgpr_dual_density]).

    The proof uses Federer 4.1.5 ([dgpr_functional_representation],
    DgprFunctionals.v) with the continuous dual Y* of 2.4.12 and its weak
    topology of 4.1.1. The representation lives on the current domain of
    R^n; its measure ρ is carried to R^n by the inclusion, a proper
    continuous injection (Federer 2.2.17, p. 72, and 2.4.18(1), p. 90).
    The image measure represents the variation of Υ on K(R^n)^+, hence
    equals ‖Υ‖ by [dgpr_variation_measure_unique] (Federer 2.5.14,
    p. 107). The density takes values in
    the closed unit ball of Y*; the norm of Federer 1.7.9 on Hom(Y, R)
    does not exceed the dual norm ([dgpr_covector_norm_le]), and the weak
    measurability of the density gives measurability in the norm
    topology because Hom(Y, R) has the finite basis dual to a basis of Y
    ([dgpr_dual_field_measurable]). *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LinearBasis HomInner ScalarInnerProduct
  FiniteDualDimension OrthonormalFamilies PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition MeasureUP MeasureBasic MeasureAlmostUP MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP RadonMeasureUP
  FunctionLatticeUP CompactSupportFunctionUP RealFunctionalNormUP ContinuousDualUP ContinuousDualSealed
  WeakEvaluationTopologyUP WeakEvaluationTopologySealed OpenFamilyTopologyMathcomp
  WeakEvaluationMeasurableCoordinates FiniteScalarContinuousCombination VectorDaniellHypotheses
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionVariationUP
  DistributionVariationDomain DistributionFiniteVariationUP DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP DistributionIntegralFieldUP CurrentDomain
  EuclideanFullDomainMeasure NormDifferentialUP NormOpenDomainLaws IsotropyGroupTopology
  CompactContinuousSubspaceSupport OpenSubspaceExtension FiniteNormEquivalence MeasurePushforward
  InjectivePushforwardIntegral RadonProperPushforward ProperMapUP RealMetricBackground.
From DPGPR Require Import DgprStanding DgprFunctionals DgprMainHypotheses DgprHomNorms
  DgprOrthonormalCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CovectorNorm.
Variable R : realType.
Variable Y : lmodType R.
Variable CY : Y -> Y -> R.
Hypothesis hCY : is_inner_product CY.
Variable d : nat.
Variable eY : 'I_d -> Y.
Hypothesis heY : is_basis eY.
Local Notation NY := (inner_norm hCY).
Local Notation ND := (hom_norm hCY (scalar_inner_productP R) heY).

(** Source for [dgpr_covector_norm_le]: blueprint mr:notation and
    mr:functionals; supporting lemma. For ψ ∈ Hom(Y, R) and 0 ≤ c with
    |ψ(y)| ≤ c |y| for y ∈ Y, the norm |ψ| of Federer 1.7.9 satisfies
    |ψ| ≤ c. Indeed, for an orthonormal basis u of Y and
    v = ∑_j ψ(u_j) u_j, we have |ψ|² = ∑_j ψ(u_j)² = ψ(v) and |v| = |ψ|
    (Federer 1.7.9, p. 35, and 1.7.5), so |ψ|² ≤ c |ψ|. *)
Lemma dgpr_covector_norm_le (psi : Hom Y R^o) (c : R) :
  0 <= c -> (forall y, `|psi y| <= c * NY y) -> ND psi <= c.
Proof.
move=> hc hb.
have [u [hu ho]] := dgpr_orthonormal_basis_exists hCY heY.
pose v := \sum_j psi (u j) *: u j.
have e1 : ND psi ^+ 2 = \sum_j psi (u j) * psi (u j) :=
  dgpr_hom_norm_sqr hCY (scalar_inner_productP R) heY psi hu ho.
have e2 : psi v = \sum_j psi (u j) * psi (u j).
  rewrite -[LHS]/(hom_as_linear psi v) /v linear_sum; apply: eq_bigr => j _.
  by rewrite linearZ hom_as_linearE.
have e3 : NY v = ND psi.
  apply: inner_norm_value; first exact: inner_norm_nonnegative.
  rewrite e1 (dgpr_orthonormal_parseval hCY hu ho v); apply: eq_bigr => j _.
  by rewrite /v (dgpr_orthonormal_coefficient hCY ho) expr2.
have e4 : ND psi * ND psi <= c * ND psi.
  rewrite -expr2 e1 -e2 -e3; apply: le_trans (hb v); exact: ler_norm.
have hN0 : 0 <= ND psi := inner_norm_nonnegative _ _.
have [hz|hp] := eqVneq (ND psi) 0; first by rewrite hz.
have hpos : 0 < ND psi by rewrite lt_neqAle eq_sym hp hN0.
by rewrite ler_pM2r in e4.
Qed.
End CovectorNorm.

Section DualFieldMeasurable.
Variable R : realType.
Variable Y : lmodType R.
Variable CY : Y -> Y -> R.
Hypothesis hCY : is_inner_product CY.
Variable d : nat.
Variable eY : 'I_d -> Y.
Hypothesis heY : is_basis eY.
Local Notation BD := (hom_inner_productP hCY (scalar_inner_productP R) heY).
Local Notation hND := (inner_norm_real_norm BD).
Variable D : lmodType R.
Variable ed : Hom D (Hom Y R^o).
Variable O : set (set D).
Hypothesis hO : is_weak_evaluation_topology (fun a y => ed a y) O.

(** Source for [dgpr_covector_expansion]: Federer 1.1.4, p. 11, the
    dual basis: ψ = ∑_i ψ(e_i) e^i for ψ ∈ Hom(Y, R), where e^i is the
    basis dual to e; supporting blueprint mr:functionals. *)
Lemma dgpr_covector_expansion (psi : Hom Y R^o) :
  psi = \sum_i psi (eY i) *: dual_basis heY i.
Proof.
apply: hom_ext => y.
have h := basis_linear_ext heY (hom_as_linear psi)
  (hom_as_linear (\sum_i psi (eY i) *: dual_basis heY i)) _ y.
rewrite !hom_as_linearE in h; apply: h => j.
by rewrite !hom_as_linearE dual_sum_evaluate.
Qed.

(** Source for [dgpr_dual_field_measurable]: blueprint mr:functionals,
    "a ‖Θ‖ measurable map into Hom(Z, R)"; supporting lemma. If k is a
    ρ measurable map into the continuous dual with its weak topology
    (Federer 4.1.1, 4.1.5) and ρ is a Radon measure, then the map
    [x ↦ ed(k(x))] into Hom(Y, R) with the norm of Federer 1.7.9 is ρ
    measurable: its coordinates ed(k(x))(e_i) are ρ measurable, and
    ed(k(x)) = ∑_i ed(k(x))(e_i) e^i (Federer 2.3.8, pp. 78-79). *)
Lemma dgpr_dual_field_measurable (T : topologicalType) (rho : set T -> \bar R) (k : T -> D) :
  is_measure rho -> is_radon_measure rho ->
  is_measure_measurable_function rho
    (partial_function_total (fun x => (k x : open_family_topological_space hO.1))) ->
  is_measure_measurable_function rho
    (partial_function_total (fun x => (ed (k x) : real_norm_metric_space hND))).
Proof.
move=> hm hr hk.
have e : (fun x => ed (k x)) = (fun x => \sum_i ed (k x) (eY i) *: dual_basis heY i).
  by apply: funext => x; exact: dgpr_covector_expansion.
rewrite e.
apply: (@finite_scalar_continuous_combination_measurable R T _ _ hND
  (dgpr_dual_space_separable hCY heY) d (fun i x => ed (k x) (eY i))
  (fun i _ => dual_basis heY i) _ rho hm hr).
- by move=> i; exact: cst_continuous.
- by move=> i; exact: (weak_evaluation_measurable_coordinates hm hk (eY i)).
Qed.
End DualFieldMeasurable.

Section ValuePushforward.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NT := (real_norm_metric_space hN).
Local Notation FT := (current_domain R n setT).
Variable rho : set FT -> \bar R.
Hypothesis hm : is_measure rho.
Local Notation nu := (measure_pushforward (set_val : FT -> NT) rho).

(** Source for [dgpr_value_pushforward_measurable]: Federer 2.1.2,
    p. 54, the image measure: a set A ⊆ R^n is measurable with respect
    to the image of ρ under the inclusion of the current domain of R^n
    into R^n whenever its inverse image is ρ measurable; supporting
    blueprint mr:functionals. *)
Lemma dgpr_value_pushforward_measurable (A : set NT) :
  measure_measurable rho (set_val @^-1` A) -> measure_measurable nu A.
Proof.
move=> hA T; rewrite /measure_pushforward (hA (set_val @^-1` T)).
congr (_ + _)%E; congr rho; by apply/seteqP; split.
Qed.

(** Source for [dgpr_value_pushforward_measurable_function]: Federer
    2.3.2, p. 73, with 2.1.2: a map F on R^n is measurable with respect
    to the image of ρ under the inclusion of the current domain whenever
    its composition with the inclusion is ρ measurable; supporting
    blueprint mr:functionals. *)
Lemma dgpr_value_pushforward_measurable_function (Z : topologicalType) (F : NT -> Z) :
  is_measure_measurable_function rho (partial_function_total (fun y : FT => F (set_val y))) ->
  is_measure_measurable_function nu (partial_function_total F).
Proof.
move=> [_ ho]; split.
- rewrite /measure_almost_everywhere /measure_pushforward.
  have -> : (set_val : FT -> NT) @^-1` (~` partial_function_domain (partial_function_total F)) =
      set0.
    apply/seteqP; split=> // y hy; exfalso; apply: hy; by exists (F (set_val y)).
  exact: measure_empty hm.
- move=> U hU; apply: dgpr_value_pushforward_measurable; exact: ho U hU.
Qed.

(** Source for [dgpr_value_pushforward_integral]: Federer 2.4.18(1),
    p. 90, for the injective inclusion of the current domain of R^n
    into R^n: an integral of F composed with the inclusion with respect
    to ρ is an integral of F with respect to the image measure;
    supporting blueprint mr:functionals. *)
Lemma dgpr_value_pushforward_integral (F : NT -> R) (b : \bar R) :
  is_measure_integral rho (real_total_integrand (fun y : FT => F (set_val y))) b ->
  is_measure_integral nu (real_total_integrand F) b.
Proof.
move=> h.
have hInj : injective (set_val : FT -> NT) by move=> x y; exact: val_inj.
apply: (injective_pushforward_integral_iff hm (real_total_integrand F) hInj b).1.
apply: (measure_integral_graph_equivalent _ h) => y z.
change (partial_function_graph (real_total_integrand (fun y : FT => F (set_val y))) y z <->
  partial_function_graph (real_total_integrand F) (set_val y) z).
by rewrite !real_total_integrand_graph.
Qed.

Hypothesis hr : is_radon_measure rho.

(** Source for [dgpr_value_pushforward_radon]: Federer 2.2.17, p. 72:
    the image of the Radon measure ρ under the inclusion of the current
    domain of R^n into R^n, a proper continuous map, is a Radon
    measure; supporting blueprint mr:functionals. *)
Lemma dgpr_value_pushforward_radon : is_radon_measure nu.
Proof.
apply: (proper_continuous_radon_pushforward hm hr).
- exact: (@metric_hausdorff R NT).
- exact: (@finite_norm_locally_compact R X n _ (coordinate_basisP R n) _ hN).
- by move=> x; exact: set_type_val_continuous.
- by move=> C hC; exact: (set_type_compact_preimage hC (subsetT C)).
Qed.
End ValuePushforward.

Section DualDensity.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation NT := (real_norm_metric_space hN).
Local Notation FT := (current_domain R n setT).
Variable Y : lmodType R.
Variable CY : Y -> Y -> R.
Hypothesis hCY : is_inner_product CY.
Variable d : nat.
Variable eY : 'I_d -> Y.
Hypothesis heY : is_basis eY.
Local Notation NY := (inner_norm hCY).
Local Notation hNY := (inner_norm_real_norm hCY).
Local Notation BD := (hom_inner_productP hCY (scalar_inner_productP R) heY).
Local Notation ND := (hom_norm hCY (scalar_inner_productP R) heY).
Local Notation hND := (inner_norm_real_norm BD).
Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space hN hNY setT ev.
Variable Ups : Hom (smooth_test_space hE) R^o.
Variable ups : set NT -> \bar R.
Hypothesis hum : is_measure ups.
Hypothesis hur : is_radon_measure ups.
Hypothesis hug : forall f,
  positive_function_lattice (@compactly_supported_continuous_functions R NT) f ->
  exists b : R, is_distribution_variation_value NY (smooth_test_values_hom hE) Ups f b%:E /\
    is_measure_integral ups (real_total_integrand f) b%:E.

Let hOutside : forall (phi : smooth_test_space hE) (x : NT), ~ setT x ->
  smooth_test_values_hom hE phi x = 0.
Proof. by move=> phi x hx; exfalso; exact: hx. Qed.

(** Source for [dgpr_ups_finite_variation]: blueprint mr:functionals,
    "Υ is representable by integration": ‖Υ‖(f) < ∞ for every
    f ∈ K(R^n)^+ (Federer 4.1.5, p. 349), since ‖Υ‖(f) is the integral
    of f with respect to the Radon measure ‖Υ‖. The variation on the
    current domain of R^n is that of the zero extension
    ([distribution_domain_gauge_value]). *)
Lemma dgpr_ups_finite_variation :
  is_finite_distribution_variation (X := NT) setT NY (smooth_test_values_hom hE) Ups.
Proof.
move=> f hf.
have hK := @open_extension_compact R NT (@metric_hausdorff R NT) setT openT f hf.1.
have hF : positive_function_lattice (@compactly_supported_continuous_functions R NT)
    (open_extension f).
  split=> // x; rewrite /open_extension; case: pselect => h; last exact: lexx.
  exact: hf.2.
have [b [hb _]] := hug hF.
by exists b; apply/(distribution_domain_gauge_value hNY hOutside Ups f b%:E).
Qed.

(** Source for [dgpr_dual_density]: blueprint mr:functionals, first
    paragraph, with Federer 4.1.5, pp. 349-350, and 2.5.14, p. 107: for
    the Radon measure ‖Υ‖ of mr:hypotheses_main there is a map
    dΥ : R^n → Hom(Y, R) which is ‖Υ‖ measurable into Hom(Y, R) with the
    norm of Federer 1.7.9, satisfies ‖dΥ(z)‖ ≤ 1 for every z, and
    Υ(g) = ∫ ⟨g(z), dΥ(z)⟩ d‖Υ‖ z for every g ∈ D(R^n, Y). These are
    the conditions on dΥ in the hypotheses (S) of mr:standing. *)
Theorem dgpr_dual_density : exists dups : X -> Hom Y R^o,
  [/\ is_measure_measurable_function ups
        (partial_function_total (fun z => (dups z : real_norm_metric_space hND))),
      (forall z, ND (dups z) <= 1) &
      (forall g : smooth_test_space hE, is_measure_integral ups
        (real_total_integrand (fun z => dups z (smooth_test_value hE g z))) (Ups g)%:E)].
Proof.
pose D := ContinuousDual.space hNY.
pose ed := ContinuousDual.evaluation hNY.
have hD := ContinuousDual.laws hNY.
pose O := WeakEvaluationTopology.opens (fun (a : D) (y : Y) => ed a y).
have hO := WeakEvaluationTopology.laws (fun (a : D) (y : Y) => ed a y).
have hU : forall x : X, setT x -> norm_domain_interior N setT x.
  by move=> x _; exact: norm_full_domain_interior.
have [rho [k hrep]] := dgpr_functional_representation heY hU hD hO dgpr_ups_finite_variation.
have hlaws := normalised_distribution_representation_laws hrep.
have hrm := distribution_representation_measure hlaws.
have hrr := distribution_representation_radon hlaws.
pose nu := measure_pushforward (set_val : FT -> NT) rho.
have hnm : is_measure nu := measure_pushforward_is_measure _ hrm.
have hnr : is_radon_measure nu := dgpr_value_pushforward_radon hrm hrr.
have hnu : ups = nu.
  apply: (dgpr_variation_measure_unique
    (@finite_norm_locally_compact R X n _ (coordinate_basisP R n) _ hN) hum hur hnm hnr hug).
  move=> f hf.
  have hfr : positive_function_lattice (@compactly_supported_continuous_functions R FT)
      (fun y : FT => f (set_val y)).
    split; first exact: (compact_scalar_open_restriction hf.1 (subsetT _)).
    by move=> y; exact: hf.2.
  have [b [hgb hib]] := normalised_distribution_original_gauge hrep hfr.
  exists b; split; last exact: (@dgpr_value_pushforward_integral R n rho hrm f b%:E hib).
  have h := (distribution_domain_gauge_value hNY hOutside Ups _ b%:E).1 hgb.
  by rewrite (compact_scalar_open_restriction_inverse (subsetT _)) in h.
pose p := @euclidean_full_domain_point R n.
pose dups := fun z : X => ed (k (p z)).
have hpv (y : FT) : p (set_val y) = y by apply: val_inj.
exists dups; split.
- rewrite hnu; apply: (dgpr_value_pushforward_measurable_function hrm).
  have e : (fun y : FT => (dups (set_val y) : real_norm_metric_space hND)) =
      (fun y => ed (k y)) by apply: funext => y; rewrite /dups hpv.
  rewrite e.
  exact: (dgpr_dual_field_measurable hCY heY hrm hrr
    (distribution_representation_weak_measurable hlaws)).
- move=> z; apply: le_trans (normalised_distribution_density_unit_bound hrep (p z)).
  have hn := continuous_dual_norm_laws hD (k (p z)).
  apply: (@dgpr_covector_norm_le R Y CY hCY d eY heY (dups z) _
    (real_functional_norm_nonnegative hn)) => y.
  by have := real_functional_norm_bound hn y; rewrite hom_as_linearE.
- move=> g; rewrite hnu; apply: (dgpr_value_pushforward_integral hrm).
  have h := distribution_representation_action hlaws g.
  have e : (fun y : FT => dups (set_val y) (smooth_test_value hE g (set_val y))) =
      (fun y => ed (k y) (@distribution_domain_values R NT setT Y (smooth_test_space hE)
        (smooth_test_values_hom hE) g y)).
    by apply: funext => y; rewrite /dups hpv.
  by rewrite e.
Qed.
End DualDensity.
