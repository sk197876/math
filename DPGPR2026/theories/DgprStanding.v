(** De Philippis, Gennaioli, Pigati and Rindler (2026), beginning of
    section 3: the standing hypotheses; blueprint dgpr_blueprint.tex,
    mr:standing, the hypotheses (S).

    The data are parameters of the predicate [dgpr_standing]: the
    dimensions n, m with 1 <= m <= n; a finite dimensional inner product
    space Y (inner product CY, basis eY); the set K of linear maps; the
    numbers lambda, Lambda; the probability measure mu with support in the
    closed ball B(0,r0); the map X : R^n -> K; the distribution Upsilon of
    type Y on R^n (Federer 4.1.1, [smooth_test_space]); its variation
    measure ||Upsilon|| and the polar dUpsilon (blueprint mr:functionals);
    delta = ||Upsilon||(R^n); T; mu0 and gamma = mu0(R^n).

    Hom(R^n,Y) carries the inner product A . B = trace(A* o B) of Federer
    1.7.9 and its norm |A|; Hom(Y,R) carries the same inner product, whose
    norm is the operator norm ||psi|| of covectors. The functional sigma
    is not a separate object: Upsilon(g) = -sigma(Dg) is stated as the
    assertion that X . Dg is mu summable with integral -Upsilon(g).
    ||Upsilon|| is represented as in blueprint mr:functionals: a Radon
    measure over R^n whose integrals of nonnegative continuous functions
    with compact support are the values of the variation ||Upsilon||(f) of
    Federer 4.1.5, and dUpsilon is a ||Upsilon|| measurable map into
    Hom(Y,R) with ||dUpsilon(z)|| <= 1 for every z and
    Upsilon(g) = integral of <g(z), dUpsilon(z)> d ||Upsilon|| z. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LinearBasis HomInner ScalarInnerProduct
  InnerConvex FiniteDualDimension HomSpaceNormTopology FiniteNormMetricPolish CompleteMetricUP
  VectorDaniellHypotheses PartialFunctionUP PartialFunctionBasic MeasureUP MeasureAlmostUP
  MeasurableFunctionUP MeasureIntegralUP SummableRealFunctionUP RadonMeasureUP FunctionLatticeUP
  CompactSupportFunctionUP DistributionVariationUP SmoothFunctionSpaceUP SmoothTestSpaces
  SmoothTestEvaluation NormDifferentialUP.
From DPGPR Require Import DgprSingularValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Standing.
Variable R : realType.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Variable Y : lmodType R.
Variable CY : Y -> Y -> R.
Hypothesis hCY : is_inner_product CY.
Variable d : nat.
Variable eY : 'I_d -> Y.
Hypothesis heY : is_basis eY.
Hypothesis hm : (0 < m <= n)%N.
Local Notation NY := (inner_norm hCY).
Local Notation hNY := (inner_norm_real_norm hCY).
Local Notation BH := (hom_inner_productP BX hCY heX).
Local Notation NH := (hom_norm BX hCY heX).
Local Notation hNH := (inner_norm_real_norm BH).
Local Notation BD := (hom_inner_productP hCY (scalar_inner_productP R) heY).
Local Notation ND := (hom_norm hCY (scalar_inner_productP R) heY).
Local Notation hND := (inner_norm_real_norm BD).
Variable K : set (real_norm_metric_space hNH).
Variables lam Lam : R.
Variable mu : set X -> \bar R.
Variable r0 : R.
Variable Xf : X -> Hom X Y.
Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space hN hNY setT ev.
Variable Ups : Hom (smooth_test_space hE) R^o.
Variable ups : set (real_norm_metric_space hN) -> \bar R.
Variable dups : X -> Hom Y R^o.
Variable delta : R.
Variable T : R.
Variable mu0 : set X -> \bar R.
Variable gamma : R.

(** Source for [dgpr_standing]: DPGPR 2026, beginning of section 3, and
    blueprint mr:standing, the hypotheses (S). K is a nonempty compact
    convex subset of Hom(R^n,Y) with sv_m(X) >= lambda and |X| <= Lambda
    for X in K (def:sv); mu is a Borel measure with mu(R^n) = 1 and
    mu(R^n - B(0,r0)) = 0; X : R^n -> K is mu measurable; Upsilon(g) =
    -sigma(Dg) = -(integral of X(x) . Dg(x) d mu x) for every test function
    g; ||Upsilon|| is the Radon variation measure of Upsilon with
    ||Upsilon||(R^n) = delta, and dUpsilon its polar with
    ||dUpsilon(z)|| <= 1 (mr:functionals, Federer 4.1.5); 0 < T; mu0 is a
    Borel measure with mu0 <= mu and gamma = mu0(R^n) > 0. *)
Record dgpr_standing : Prop := {
  dgpr_standing_K_nonempty : exists A, K A;
  dgpr_standing_K_compact : compact K;
  dgpr_standing_K_convex : is_inner_convex K;
  dgpr_standing_lambda : 0 < lam;
  dgpr_standing_Lambda : 0 < Lam;
  dgpr_standing_K_sv : forall A, K A -> lam <= dgpr_sv BX hCY heX hm A;
  dgpr_standing_K_norm : forall A, K A -> NH A <= Lam;
  dgpr_standing_mu_measure : is_measure mu;
  dgpr_standing_mu_borel : forall A : set (real_norm_metric_space hN), open A -> measure_measurable mu A;
  dgpr_standing_mu_mass : mu setT = 1%:E;
  dgpr_standing_r0 : 0 < r0;
  dgpr_standing_mu_support : measure_almost_everywhere mu [set y | N y <= r0];
  dgpr_standing_X_measurable : is_measure_measurable_function mu
    (partial_function_total (fun y => (Xf y : real_norm_metric_space hNH)));
  dgpr_standing_X_values : forall y, K (Xf y);
  dgpr_standing_constraint : forall (g : smooth_test_space hE) (Dg : X -> Hom X Y),
    (forall x, has_norm_differential N NY setT (smooth_test_value hE g) x (Dg x)) ->
    is_measure_integral mu (real_total_integrand (fun x => hom_inner BX hCY heX (Xf x) (Dg x)))
      (- Ups g)%:E;
  dgpr_standing_ups_measure : is_measure ups;
  dgpr_standing_ups_radon : is_radon_measure ups;
  dgpr_standing_ups_gauge : forall f,
    positive_function_lattice (@compactly_supported_continuous_functions R (real_norm_metric_space hN)) f ->
    exists b : R, is_distribution_variation_value NY (smooth_test_values_hom hE) Ups f b%:E /\
      is_measure_integral ups (real_total_integrand f) b%:E;
  dgpr_standing_ups_mass : ups setT = delta%:E;
  dgpr_standing_dups_measurable : is_measure_measurable_function ups
    (partial_function_total (fun z => (dups z : real_norm_metric_space hND)));
  dgpr_standing_dups_bound : forall z, ND (dups z) <= 1;
  dgpr_standing_dups_action : forall g : smooth_test_space hE,
    is_measure_integral ups (real_total_integrand (fun z => dups z (smooth_test_value hE g z))) (Ups g)%:E;
  dgpr_standing_T : 0 < T;
  dgpr_standing_mu0_measure : is_measure mu0;
  dgpr_standing_mu0_borel : forall A : set (real_norm_metric_space hN), open A -> measure_measurable mu0 A;
  dgpr_standing_mu0_le : forall A, (mu0 A <= mu A)%E;
  dgpr_standing_mu0_mass : mu0 setT = gamma%:E;
  dgpr_standing_gamma : 0 < gamma
}.

End Standing.

Section Spaces.
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
Local Notation hNH := (inner_norm_real_norm BH).
Local Notation BD := (hom_inner_productP hCY (scalar_inner_productP R) heY).
Local Notation hND := (inner_norm_real_norm BD).

(** Source for [dgpr_hom_space_complete]: Hom(R^n,Y) with the norm of
    Federer 1.7.9 is complete, since it has a finite basis (1.4.5,
    [hom_space_finite_basis]) and finite dimensional normed spaces are
    complete; supporting blueprint def:heat_objects (heat extension W). *)
Lemma dgpr_hom_space_complete : is_complete_metric_space (real_norm_metric_space hNH).
Proof.
have [k [u hu]] := hom_space_finite_basis heX heY.
exact: (@finite_norm_metric_complete _ _ _ hNH _ _ hu).
Qed.

(** Source for [dgpr_hom_space_separable]: Hom(R^n,Y) with the norm of
    Federer 1.7.9 is separable, since it has a finite basis; supporting
    blueprint def:heat_objects. *)
Lemma dgpr_hom_space_separable : is_separable_normed_space hNH.
Proof.
have [k [u hu]] := hom_space_finite_basis heX heY.
exact: (finite_norm_metric_separable hNH hu).
Qed.

(** Source for [dgpr_dual_space_complete]: Hom(Y,R) with the norm of
    Federer 1.7.9 is complete, since the dual basis of eY is a basis
    (Federer 1.1.4); supporting blueprint def:heat_objects (heat
    extension Psi). *)
Lemma dgpr_dual_space_complete : is_complete_metric_space (real_norm_metric_space hND).
Proof. exact: (@finite_norm_metric_complete _ _ _ hND _ _ (dual_basisP heY)). Qed.

(** Source for [dgpr_dual_space_separable]: Hom(Y,R) with the norm of
    Federer 1.7.9 is separable; supporting blueprint def:heat_objects. *)
Lemma dgpr_dual_space_separable : is_separable_normed_space hND.
Proof. exact: (finite_norm_metric_separable hND (dual_basisP heY)). Qed.

End Spaces.
