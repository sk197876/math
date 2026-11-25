(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3, (3.4)
    and the identity before (3.12); blueprint dgpr_blueprint.tex,
    lem:identities(spt), (div) and (divB).

    The covector div W_t(x) in Hom(Y,R) of blueprint mr:notation is given
    by its values <y, div W_t(x)> = sum_i D W_t(x)(eps_i)(eps_i) . y; the
    differential D W_t(x) enters through its values l, given by
    [dgpr_differential_values NH (fun z => W (t, z)) x l]. The same
    convention is used for div B_t(x). No vector is identified with a
    covector: Psi(t,x) and eta(t,x) are evaluated at y. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm InnerNormInequalities
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CoordinateProjection FiniteCoordinates
  LinearBasis HomInner HomInnerCoordinates OrthonormalFamilies EuclideanStiefelInnerSplitting
  ScalarInnerProduct TensorUP Bilinear CompleteMetricUP VectorDaniellHypotheses PartialFunctionUP
  PartialFunctionBasic MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralComparison MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureIntegralAlmostEquality SummableRealFunctionUP SummableRealArithmetic RadonMeasureUP
  MeasureVectorIntegralUP ContinuousRealFunctional ScalarNormMetricCompleteness LocalUniquenessExample
  FiniteNormMetricCompactness NormDifferentialUP NormDifferentialLinear NormDifferentialDirectional NormDifferentialLocalAgreement NormBoundedLinearTopology
  NormClassOneUP NormRegularity SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  DistributionVariationUP FunctionLatticeUP CompactSupportFunctionUP RealCurveDerivativeUP.
From DPGPR Require Import DgprOrthonormalCoordinates DgprHomNorms DgprSingularValue DgprHeatKernel
  DgprHeatKernelDifferential DgprHeatExtension DgprHeatSemiconvex DgprHeatExtensionBounds
  DgprDifferentialCalculus DgprHeatJets DgprBackwardHeat DgprStanding DgprHeatObjects DgprIdentities
  DgprFunctionals DgprHeatTestFunction DgprHeatJetCalculus DgprHeatCalculus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Divergence.
Variable R : realType.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Local Notation eps := (@coordinate_basis R n).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation p := (@dgpr_heat_kernel R n).
Local Notation Dp := (@dgpr_kernel_differential R n).
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
Local Notation hZ1 := (@scalar_norm_metric_complete R).
Local Notation hsep1 := (scalar_norm_separable R).
Local Notation hHc := (@dgpr_hom_space_complete R n Y CY hCY d eY heY).
Local Notation hDc := (@dgpr_dual_space_complete R Y CY hCY d eY heY).
Local Notation hHs := (@dgpr_hom_space_separable R n Y CY hCY d eY heY).
Local Notation hDs := (@dgpr_dual_space_separable R Y CY hCY d eY heY).
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
Hypothesis hS : dgpr_standing heY hm K lam Lam mu r0 Xf Ups ups dups delta T mu0 gamma.
Local Notation hmu := (dgpr_standing_mu_measure hS).
Local Notation hups := (dgpr_standing_ups_measure hS).
Local Notation hOmu := (dgpr_standing_mu_borel hS).
Local Notation hOups := (radon_open_measurable (dgpr_standing_ups_radon hS)).
Local Notation hMmu := (dgpr_standing_mu_mass hS).
Local Notation hMups := (dgpr_standing_ups_mass hS).
Local Notation W := (dgpr_heat_W hS).
Local Notation Psi := (dgpr_heat_Psi hS).
Local Notation S := (dgpr_heat_S hS).
Local Notation B := (dgpr_heat_B hS).
Local Notation eta := (dgpr_heat_eta hS).
Local Notation zeta := (dgpr_heat_zeta hS).

(** Source for [dgpr_identities_spt]: blueprint lem:identities(spt) and
    DPGPR 2026, section 3: ||Upsilon||(R^n - B(0,r0)) = 0. If a test
    function g vanishes on an open set G containing B(0,r0), then
    Dg(x) = 0 for x in G (Federer 3.1.1), hence for mu almost all x, and
    Upsilon(g) = -sigma(Dg) = 0; mr:functionals ([dgpr_variation_null_outside])
    gives the conclusion. *)
Theorem dgpr_identities_spt : ups (~` [set y | N y <= r0]) = 0%E.
Proof.
have hK := @finite_norm_metric_ball_compact R X N hN n eps heX r0.
have hC : closed ([set y | N y <= r0] : set (real_norm_metric_space hN)).
  exact: (compact_closed (@metric_hausdorff R (real_norm_metric_space hN)) hK).
have hr := dgpr_standing_ups_radon hS.
apply: (dgpr_variation_null_outside hNY hups hr (radon_locally_compact hr) (dgpr_standing_ups_gauge hS) hC).
move=> phi G hG hCG hphi.
have [Dg hDg] := (norm_class_firstP hN hNY setT (smooth_test_value hE phi)).1
  (smooth_test_value_smooth hE phi 1%N).
have hD (z : X) : has_norm_differential N NY setT (smooth_test_value hE phi) z (Dg z).
  exact: (norm_class_one_differential hDg (Logic.I : setT z)).
have hz (z : X) : G z -> Dg z = 0.
  move=> hzG.
  have hn : nbhs (z : real_norm_metric_space hN) G by apply: open_nbhs_nbhs; split.
  have [dd [hd hball]] := (norm_domain_interior_neighbourhood hN G z).2 hn.
  have hi : norm_domain_interior N setT z by exists 1; split.
  have hT := @norm_differential_constant R X Y N NY hN hNY setT z (0 : Y) hi.
  have hT' : has_norm_differential N NY setT (smooth_test_value hE phi) z 0.
    apply: (norm_differential_local_agreement hN hd _ _ hT) => h hh //.
    by move=> _; exact: (esym (hphi (z + h) (hball h hh))).
  exact: (norm_differential_unique hN hNY (hD z) hT').
have hc := dgpr_standing_constraint hS hD.
have h0 := dgpr_constant_integral hmu hMmu 0; rewrite mul0r in h0.
have hae : measure_almost_equal mu (real_total_integrand (fun _ : X => (0 : R)))
    (real_total_integrand (fun x => hom_inner BX hCY heX (Xf x) (Dg x))).
  apply: (measure_almost_everywhere_mono hmu _ (dgpr_standing_mu_support hS)) => z hzb.
  exists 0%:E; split; first exact/real_total_integrand_graph.
  apply/real_total_integrand_graph; rewrite (hz z (hCG z hzb)).
  by rewrite (bil0r (inner_bilinear BH)).
have e := measure_integral_unique hc (measure_integral_almost_equal hmu h0 hae).
by case: e => /eqP; rewrite oppr_eq0 => /eqP.
Qed.

(** Source for [dgpr_hom_apply_bound]: |A(eps_i)| <= |A| for the norm of
    Federer 1.7.9, since |A|^2 = sum_j |A(eps_j)|^2; supporting
    blueprint proof of lem:identities(div). *)
Lemma dgpr_hom_apply_bound (A : Hom X Y) (i : 'I_n) : NY (A (eps i)) <= NH A.
Proof.
apply: dgpr_sqr_le; first exact: inner_norm_nonnegative.
rewrite (dgpr_hom_norm_sqr BX hCY heX A heX (@euclidean_coordinate_orthonormal_family R n)).
rewrite (inner_norm_sqr hCY) (bigD1 i) //= lerDl.
by apply: sumr_ge0 => j _; rewrite -(inner_norm_sqr hCY) sqr_ge0.
Qed.

(** Source for [dgpr_covector_apply_bound]: |phi(w_k)| <= |phi| for an
    orthonormal basis w of Y and the norm of Federer 1.7.9 on Hom(Y,R);
    supporting blueprint proof of lem:identities(div). *)
Lemma dgpr_covector_apply_bound (phi : Hom Y R^o) (w : 'I_d -> Y) (k : 'I_d) :
  is_basis w -> orthonormal_family CY w -> `|phi (w k)| <= ND phi.
Proof.
move=> hw ho; apply: dgpr_sqr_le; first exact: inner_norm_nonnegative.
rewrite (dgpr_hom_norm_sqr hCY (scalar_inner_productP R) heY phi hw ho) (bigD1 k) //= -normrX ger0_norm ?sqr_ge0 // expr2 lerDl.
by apply: sumr_ge0 => j _; rewrite -expr2 sqr_ge0.
Qed.

(** Source for [dgpr_covector_eval_bound]: evaluation at y is a bounded
    linear functional on Hom(Y,R) (Federer 1.7.5, 1.7.9); supporting
    blueprint proof of lem:identities(div). *)
Lemma dgpr_covector_eval_bound (y : Y) :
  exists C : R, 0 <= C /\ forall phi : Hom Y R^o, `|phi y| <= C * ND phi.
Proof.
have [w [hw ho]] := dgpr_orthonormal_basis_exists hCY heY.
exists (\sum_k `|CY y (w k)|); split; first by apply: sumr_ge0 => k _; exact: normr_ge0.
move=> phi; rewrite {1}(dgpr_orthonormal_expansion hCY hw ho y) linear_sum mulr_suml.
apply: le_trans; first exact: ler_norm_sum.
apply: ler_sum => k _; rewrite linearZ.
change (`|CY y (w k) * phi (w k)| <= `|CY y (w k)| * ND phi); rewrite normrM.
by apply: ler_wpM2l; [exact: normr_ge0 | exact: dgpr_covector_apply_bound].
Qed.

(** Source for [dgpr_covector_eval]: the evaluation [phi |-> phi(y)] as
    a linear functional on Hom(Y,R); supporting blueprint proof of
    lem:identities(div). *)
Definition dgpr_covector_eval_map (y : Y) (phi : Hom Y R^o) : R^o := phi y.

(** Source for [dgpr_covector_eval_linear]: Federer 1.4.1: operations
    on Hom(Y,R) are pointwise; supporting lem:identities(div). *)
Lemma dgpr_covector_eval_linear (y : Y) : linear (dgpr_covector_eval_map y).
Proof. by move=> c phi psi; rewrite /dgpr_covector_eval_map hom_addE hom_scaleE. Qed.

(** Source for [dgpr_covector_eval]: the functional of
    [dgpr_covector_eval_map]; supporting lem:identities(div). *)
Definition dgpr_covector_eval (y : Y) : {linear Hom Y R^o -> R^o} :=
  hom_as_linear (@HomMap R (Hom Y R^o) R^o (dgpr_covector_eval_map y) (asboolT (dgpr_covector_eval_linear y))).

(** Source for [dgpr_covector_eval_continuous]: evaluation at y is a
    continuous linear functional on Hom(Y,R) (Federer 2.4.12); supporting
    lem:identities(div). *)
Lemma dgpr_covector_eval_continuous (y : Y) : is_continuous_real_functional hND (dgpr_covector_eval y).
Proof.
have [C [hC hb]] := dgpr_covector_eval_bound y.
by apply: (bounded_real_functional_continuous (C := C)) => // phi; exact: hb.
Qed.

(** Source for [dgpr_coordinate_eval_map]: the functional
    [A |-> A(eps_i) . y] on Hom(R^n,Y); supporting blueprint proof of
    lem:identities(div). *)
Definition dgpr_coordinate_eval_map (i : 'I_n) (y : Y) (A : Hom X Y) : R^o := CY (A (eps i)) y.

(** Source for [dgpr_coordinate_eval_linear]: Federer 1.4.1 and 1.7.1:
    linearity of [dgpr_coordinate_eval_map]; supporting
    lem:identities(div). *)
Lemma dgpr_coordinate_eval_linear (i : 'I_n) (y : Y) : linear (dgpr_coordinate_eval_map i y).
Proof.
move=> c A A'; rewrite /dgpr_coordinate_eval_map hom_addE hom_scaleE.
by rewrite (bilDl (inner_bilinear hCY)) (bilZl (inner_bilinear hCY)).
Qed.

(** Source for [dgpr_coordinate_eval]: the functional of
    [dgpr_coordinate_eval_map]; supporting lem:identities(div). *)
Definition dgpr_coordinate_eval (i : 'I_n) (y : Y) : {linear Hom X Y -> R^o} :=
  hom_as_linear (@HomMap R (Hom X Y) R^o (dgpr_coordinate_eval_map i y)
    (asboolT (dgpr_coordinate_eval_linear i y))).

(** Source for [dgpr_coordinate_eval_continuous]: |A(eps_i) . y| <=
    |y| |A| (Federer 1.7.1, 1.7.9), so [dgpr_coordinate_eval] is a
    continuous linear functional; supporting lem:identities(div). *)
Lemma dgpr_coordinate_eval_continuous (i : 'I_n) (y : Y) :
  is_continuous_real_functional hNH (dgpr_coordinate_eval i y).
Proof.
apply: (bounded_real_functional_continuous (C := NY y)); first exact: inner_norm_nonnegative.
move=> A; change (`|CY (A (eps i)) y| <= NY y * NH A).
apply: (le_trans (inner_cauchy hCY _ _)); rewrite [X in X <= _]mulrC.
by apply: ler_wpM2l; [exact: inner_norm_nonnegative | exact: dgpr_hom_apply_bound].
Qed.

(** Source for [dgpr_identities_div_W]: blueprint lem:identities(div),
    div W_t(x) = Psi(t,x), and DPGPR 2026, section 3. For y in Y, with
    s = T - t and the test function g of [dgpr_heat_kernel_test], equal
    to [z |-> p_s(x-z) y] near B(0,r0): by (spt), Upsilon(g) is the
    integral of p_s(x-z) <y, dUpsilon(z)> d ||Upsilon|| z, that is
    <y, Psi(t,x)>; by (S), Upsilon(g) = -sigma(Dg) is the integral of
    sum_i D p_s(x-z)(eps_i) (X(z)(eps_i) . y) d mu z; and this is
    sum_i D W_t(x)(eps_i)(eps_i) . y by lem:heat_extension(1) and
    Federer 2.4.12. *)
Theorem dgpr_identities_div_W (t : R) (x : X) (y : Y) (l : X -> Hom X Y) : t < T ->
  dgpr_differential_values NH (fun z => W (t, z)) x l ->
  \sum_(i < n) CY (l (eps i) (eps i)) y = Psi (t, x) y.
Proof.
move=> ht hl; have hs : 0 < T - t by rewrite subr_gt0.
have hXmeas := dgpr_standing_X_measurable hS.
have hXb : forall z, NH (Xf z) <= Lam := fun z => dgpr_standing_K_norm hS (dgpr_standing_X_values hS z).
have [_ [hDW _]] := dgpr_backward_heat_jet hmu hHc hOmu hMmu hHs hXmeas hXb x ht.
have el i : l (eps i) = dgpr_backward_first hmu hHc Xf T t x (eps i).
  exact: (dgpr_differential_values_unique hNH hl (hDW x)).
have hIi (i : 'I_n) : is_measure_integral mu
    (real_total_integrand (fun z => Dp (T - t) (x - z) (eps i) * CY (Xf z (eps i)) y))
    (CY (l (eps i) (eps i)) y)%:E.
  have hI := dgpr_convolution_integral hmu hHc hOmu hMmu hHs hXmeas hXb x
    (dgpr_kernel_first_class_zero (eps i) hs) (fun z => dgpr_kernel_differential_bound z (eps i) hs).
  have h := hI.2 _ (dgpr_coordinate_eval_continuous (i := i) (y := y)).
  rewrite el; apply: (measure_integral_graph_equivalent _ h) => z c; split.
  - move=> [v [hv <-]]; apply/real_total_integrand_graph; rewrite -hv.
    by rewrite /= /dgpr_coordinate_eval_map hom_scaleE (bilZl (inner_bilinear hCY)).
  - move/real_total_integrand_graph => <-; exists (Dp (T - t) (x - z) (eps i) *: Xf z); split => //.
    by rewrite /= /dgpr_coordinate_eval_map hom_scaleE (bilZl (inner_bilinear hCY)).
have hsum := dgpr_real_integral_sum hmu hIi.
have [g [Dg [Wo [hWo [hball [hDg hgW]]]]]] := dgpr_heat_kernel_test hE r0 x y hs.
have hc := dgpr_standing_constraint hS hDg.
have hpt (z : X) : N z <= r0 ->
    hom_inner BX hCY heX (Xf z) (Dg z) = - \sum_(i < n) Dp (T - t) (x - z) (eps i) * CY (Xf z (eps i)) y.
  move=> hz; have [_ hDgz] := hgW z (hball z hz).
  rewrite (hom_inner_orthonormal_sum BX hCY heX heX (@euclidean_coordinate_orthonormal_family R n)) -sumrN.
  apply: eq_bigr => i _; rewrite hDgz -scaleNr (bilZr (inner_bilinear hCY)).
  by change (- Dp (T - t) (x - z) (eps i) * CY (Xf z (eps i)) y =
    - (Dp (T - t) (x - z) (eps i) * CY (Xf z (eps i)) y)); rewrite mulNr.
have hc' := real_total_integral_scale hmu (-1) hc.
have hU1 : is_measure_integral mu
    (real_total_integrand (fun z => \sum_(i < n) Dp (T - t) (x - z) (eps i) * CY (Xf z (eps i)) y))
    (Ups g)%:E.
  have e1 : -1 * - Ups g = Ups g by rewrite mulN1r opprK.
  rewrite -e1; apply: (measure_integral_almost_equal hmu hc').
  apply: (measure_almost_everywhere_mono hmu _ (dgpr_standing_mu_support hS)) => z hz.
  exists (\sum_(i < n) Dp (T - t) (x - z) (eps i) * CY (Xf z (eps i)) y)%:E.
  split; apply/real_total_integrand_graph => //.
  by rewrite (hpt z hz) mulN1r opprK.
have e2 := measure_integral_unique hsum hU1.
have hA := dgpr_standing_dups_action hS g.
have hP := dgpr_heat_extension_integral hups hDc hOups hMups hDs (dgpr_standing_dups_measurable hS)
  (dgpr_standing_dups_bound hS) x hs.
have hPy := hP.2 _ (dgpr_covector_eval_continuous (y := y)).
have hU2 : is_measure_integral ups (real_total_integrand (fun z => p (T - t) (x - z) * dups z y))
    (Ups g)%:E.
  apply: (measure_integral_almost_equal hups hA).
  apply: (measure_almost_everywhere_mono hups _ dgpr_identities_spt) => z hz.
  exists (p (T - t) (x - z) * dups z y)%:E.
  split; apply/real_total_integrand_graph => //.
  have [hgz _] := hgW z (hball z hz).
  by rewrite hgz linearZ.
have hU3 : is_measure_integral ups (real_total_integrand (fun z => p (T - t) (x - z) * dups z y))
    (Psi (t, x) y)%:E.
  apply: (measure_integral_graph_equivalent _ hPy) => z c; split.
  - move=> [v [hv <-]]; apply/real_total_integrand_graph; rewrite -hv.
    by rewrite /= /dgpr_covector_eval_map.
  - move/real_total_integrand_graph => <-; exists (p (T - t) (x - z) *: dups z); split => //.
have e3 := measure_integral_unique hU2 hU3.
by case: e2 => ->; case: e3.
Qed.

(** Source for [dgpr_identities_div]: blueprint lem:identities(div) and
    DPGPR 2026, section 3: div W_t(x) = Psi(t,x) and
    ||Psi(t,x)|| <= R(t,x) on Omega_T. *)
Theorem dgpr_identities_div (t : R) (x : X) : t < T ->
  (forall (y : Y) (l : X -> Hom X Y), dgpr_differential_values NH (fun z => W (t, z)) x l ->
    \sum_(i < n) CY (l (eps i) (eps i)) y = Psi (t, x) y) /\
  ND (Psi (t, x)) <= dgpr_heat_R hS (t, x).
Proof.
move=> ht; split; first by move=> y l; exact: dgpr_identities_div_W.
exact: dgpr_identities_Psi_bound.
Qed.

(** Source for [dgpr_identities_divB]: blueprint lem:identities(divB),
    DPGPR 2026, section 3, and Gennaioli 2026, (3.9): for (t,x) in
    Omega_T and y in Y, <y, div B_t(x)> + B(t,x)(zeta(t,x)) . y =
    <y, eta(t,x)>. Since B = S^(-1) W, the Leibniz formula (Federer
    3.1.11) gives D B_t(x)(v) = S^(-1) D W_t(x)(v) - S^(-2)
    D S_t(x)(v) W(t,x); moreover sum_i D S_t(x)(eps_i) W(t,x)(eps_i) =
    W(t,x)(grad S_t(x)) and grad S_t(x) = S(t,x) zeta(t,x); combine with
    (div). *)
Theorem dgpr_identities_divB (t : R) (x : X) (y : Y) (l : X -> Hom X Y) : t < T ->
  dgpr_differential_values NH (fun z => B (t, z)) x l ->
  \sum_(i < n) CY (l (eps i) (eps i)) y + CY (B (t, x) (zeta (t, x))) y = eta (t, x) y.
Proof.
move=> ht hl.
have hpos z : 0 < S (t, z) := dgpr_identities_S_pos hS z ht.
have hS0 := hpos x.
have [hinv1 hinv2] := @dgpr_real_curve_inverse R.
have jI := dgpr_heat_jet_compose hinv1 hinv2 hpos (dgpr_heat_S_jet hS x ht).
have jW := dgpr_backward_heat_jet hmu hHc hOmu hMmu hHs (dgpr_standing_X_measurable hS)
  (fun z => dgpr_standing_K_norm hS (dgpr_standing_X_values hS z)) x ht.
have [_ [hDB _]] := dgpr_heat_jet_scalar_product hNH jI jW.
have [_ [hDW _]] := jW.
have el i : l (eps i) =
    (- (S (t, x)) ^- 2 * dgpr_heat_S_first hS t x (eps i)) *: W (t, x) +
    (S (t, x))^-1 *: dgpr_backward_first hmu hHc Xf T t x (eps i).
  exact: (dgpr_differential_values_unique hNH hl (hDB x)).
have hdiv := @dgpr_identities_div_W t x y _ ht (hDW x).
have e1 i : CY (l (eps i) (eps i)) y =
    - (S (t, x)) ^- 2 * (dgpr_heat_S_first hS t x (eps i) * CY (W (t, x) (eps i)) y) +
    (S (t, x))^-1 * CY (dgpr_backward_first hmu hHc Xf T t x (eps i) (eps i)) y.
  rewrite el hom_addE !hom_scaleE (bilDl (inner_bilinear hCY)) !(bilZl (inner_bilinear hCY)).
  by rewrite mulrA.
have eW : W (t, x) (dgpr_gradient_values (dgpr_heat_S_first hS t x)) =
    \sum_(i < n) dgpr_heat_S_first hS t x (eps i) *: W (t, x) (eps i).
  by rewrite /dgpr_gradient_values linear_sum; apply: eq_bigr => i _; rewrite linearZ.
rewrite (eq_bigr _ (fun i _ => e1 i)) big_split /= -!mulr_sumr hdiv.
rewrite -(dgpr_inner_suml hCY) -eW (dgpr_heat_S_gradient hS x ht) linearZ (bilZl (inner_bilinear hCY)).
have eB : CY (B (t, x) (zeta (t, x))) y = (S (t, x))^-1 * CY (W (t, x) (zeta (t, x))) y.
  transitivity (CY ((S (t, x))^-1 *: W (t, x) (zeta (t, x))) y).
    by congr (CY _ y); exact: (hom_scaleE (S (t, x))^-1 (W (t, x)) (zeta (t, x))).
  exact: (bilZl (inner_bilinear hCY)).
rewrite eB.
change (- (S (t, x)) ^- 2 * (S (t, x) * CY (W (t, x) (zeta (t, x))) y) +
  (S (t, x))^-1 * Psi (t, x) y + (S (t, x))^-1 * CY (W (t, x) (zeta (t, x))) y =
  (S (t, x))^-1 * Psi (t, x) y).
have e (s a b : R) : 0 < s -> - s ^- 2 * (s * a) + s^-1 * b + s^-1 * a = s^-1 * b.
  move=> hs; rewrite mulrA mulNr expr2 invfM -mulrA mulVf ?gt_eqF // mulr1; ring.
exact: (e _ _ _ hS0).
Qed.

End Divergence.
