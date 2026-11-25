(** De Philippis, Gennaioli, Pigati and Rindler (2026), proof of
    Lemma 3.1; blueprint dgpr_blueprint.tex, proof of lem:DGPR31: the
    pointwise identities and inequalities on Omega_T used in that proof,
    namely H(rho log q) = kappa rho + rho |grad log q|^2,
    H(rho |B|^2) = 2 rho |DB|^2 + 2 rho grad log q . grad |B|^2 +
    2 kappa rho |B|^2, and the bound of |B(grad log rho)|^2 obtained from
    lem:identities(divB). Differentials enter through their values, as in
    DgprHeatJets.v. *)
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
  DistributionVariationUP FunctionLatticeUP CompactSupportFunctionUP RealCurveDerivativeUP
  RealExponentialUP RealExponentialSealed HomNormBound.
From DPGPR Require Import DgprOrthonormalCoordinates DgprHomNorms DgprSingularValue DgprHeatKernel
  DgprHeatKernelDifferential DgprHeatExtension DgprHeatSemiconvex DgprHeatExtensionBounds
  DgprDifferentialCalculus DgprHeatJets DgprBackwardHeat DgprStanding DgprHeatObjects DgprIdentities
  DgprFunctionals DgprHeatTestFunction DgprHeatJetCalculus DgprHeatCalculus DgprIdentitiesDivergence
  DgprHeatKernelFamily DgprMeasureComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section EntropyCurves.
Variable R : realType.
Local Notation LOG := (@RealExponential.logarithm R).

(** Source for [dgpr_entropy_curve1]: Phi(r) = r log r on (0,infinity)
    has Phi'(r) = log r + 1 (Federer 3.1.1); proof of lem:DGPR31, the
    function Phi of lem:heat_calculus(chain). *)
Lemma dgpr_entropy_curve1 (r : R) : 0 < r ->
  has_real_curve_derivative (fun s => s * LOG s) r (LOG r + 1).
Proof.
move=> hr; have [hl _] := @dgpr_real_curve_logarithm R.
have hid : has_real_curve_derivative (fun s : R => s) r 1.
  have h := dgpr_real_curve_affine 0 1 r.
  have e : (fun t : R => 0 + t * 1) = (fun s : R => s) by apply: funext => s; rewrite add0r mulr1.
  by rewrite e in h.
have h := dgpr_real_curve_product hid (hl r hr).
by rewrite mul1r mulfV ?gt_eqF in h.
Qed.

(** Source for [dgpr_entropy_curve2]: Phi'(r) = log r + 1 has
    Phi''(r) = r^(-1) on (0,infinity) (Federer 3.1.1); proof of
    lem:DGPR31. *)
Lemma dgpr_entropy_curve2 (r : R) : 0 < r ->
  has_real_curve_derivative (fun s => LOG s + 1) r r^-1.
Proof.
move=> hr; have [hl _] := @dgpr_real_curve_logarithm R.
have h := dgpr_real_curve_add (hl r hr) (dgpr_real_curve_constant 1 r).
by rewrite addr0 in h.
Qed.
End EntropyCurves.

Section SumSquares.
Variable R : realType.
Variable n : nat.

(** Source for [dgpr_sum_sqr_le]: (a_1 + ... + a_n)^2 <= n (a_1^2 + ... +
    a_n^2), the Cauchy-Schwarz inequality of Federer 1.7.1 in R^n;
    supporting blueprint proof of lem:DGPR31. *)
Lemma dgpr_sum_sqr_le (a : 'I_n -> R) : (\sum_i a i) ^+ 2 <= n%:R * \sum_i a i ^+ 2.
Proof.
pose u : R_n R n := [ffun i => a i]; pose v : R_n R n := [ffun _ => 1].
have h := inner_cauchy (@euclidean_inner_productP R n) u v.
have e1 : euclidean_inner_product u v = \sum_i a i.
  by rewrite /euclidean_inner_product; apply: eq_bigr => i _; rewrite !ffunE mulr1.
have e2 : euclidean_inner_product u u = \sum_i a i ^+ 2.
  by rewrite /euclidean_inner_product; apply: eq_bigr => i _; rewrite !ffunE expr2.
have e3 : euclidean_inner_product v v = n%:R.
  rewrite /euclidean_inner_product (eq_bigr (fun _ => 1)); last by move=> i _; rewrite !ffunE mulr1.
  by rewrite sumr_const card_ord.
rewrite e1 in h.
have hN0 := inner_norm_nonnegative (@euclidean_inner_productP R n).
have h2 : `|\sum_i a i| ^+ 2 <= (inner_norm (@euclidean_inner_productP R n) u *
    inner_norm (@euclidean_inner_productP R n) v) ^+ 2.
  by apply: lerXn2r; rewrite ?nnegrE ?normr_ge0 ?mulr_ge0.
rewrite -normrX ger0_norm ?sqr_ge0 // exprMn !(inner_norm_sqr (@euclidean_inner_productP R n)) in h2.
by rewrite mulrC -e3 -e2.
Qed.
End SumSquares.

Section Lemma31Pointwise.
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

Local Notation U := (dgpr_heat_U hS).
Local Notation Rr := (dgpr_heat_R hS).
Local Notation rho := (dgpr_heat_rho hS).
Local Notation kappa := (dgpr_heat_kappa hS).
Local Notation Q := (dgpr_heat_q hS).
Local Notation LOG := (@RealExponential.logarithm R).

(** Source for [dgpr_lemma31_heat_entropy]: blueprint proof of
    lem:DGPR31 and DPGPR 2026, proof of Lemma 3.1:
    H(rho log q) = kappa rho + rho |grad log q|^2 on Omega_T, from
    lem:heat_calculus(S), (chain) and (Bq) with f = q log q and
    Phi(r) = r log r, since S q = rho; here grad log q_t(x) =
    q(t,x)^(-1) grad q_t(x) and l are the values of D q_t(x). *)
Theorem dgpr_lemma31_heat_entropy (t : R) (x : X) (l : X -> R) : t < T ->
  @dgpr_differential_values R n R^o A1 (fun z => Q (t, z)) x l ->
  @dgpr_heat_operator R n R^o A1 (fun p : TX => rho p * LOG (Q p)) t x
    (kappa (t, x) * rho (t, x) + rho (t, x) * N ((Q (t, x))^-1 *: dgpr_gradient_values l) ^+ 2).
Proof.
move=> ht hl.
have hS0 z : 0 < S (t, z) := dgpr_identities_S_pos hS z ht.
have hr0 z : 0 < rho (t, z) := dgpr_identities_rho_pos hS z ht.
have hQ0 z : 0 < Q (t, z) by rewrite /dgpr_heat_q divr_gt0.
have [_ hQ] := dgpr_heat_calculus_Bq hS x ht.
have hc := dgpr_heat_calculus_chain (@dgpr_entropy_curve1 R) (@dgpr_entropy_curve2 R) hQ0 hQ hl.
have hSf := dgpr_heat_calculus_S hA ht hc.
have hfg (p : TX) : p.1 < T -> S p *: (Q p * LOG (Q p) : R^o) = (rho p * LOG (Q p) : R^o).
  case: p => r z /= hr; have hSz := dgpr_identities_S_pos hS z hr.
  change (S (r, z) * (Q (r, z) * LOG (Q (r, z))) = rho (r, z) * LOG (Q (r, z))).
  by rewrite mulrA /dgpr_heat_q mulrCA mulfV ?gt_eqF ?mulr1.
have hloc := dgpr_heat_operator_local ht hfg hSf.
have hval (h h' : R^o) : h = h' ->
    @dgpr_heat_operator R n R^o A1 (fun p : TX => (rho p * LOG (Q p) : R^o)) t x h ->
    @dgpr_heat_operator R n R^o A1 (fun p : TX => (rho p * LOG (Q p) : R^o)) t x h'.
  by move=> ->.
apply: (hval _ _ _ hloc).
rewrite (real_seminorm_scale hN.1) gtr0_norm ?invr_gt0 //.
have er : rho (t, x) = S (t, x) * Q (t, x).
  by rewrite /dgpr_heat_q mulrCA mulfV ?gt_eqF ?mulr1.
have e (s q k G : R) : 0 < q ->
    s * ((LOG q + 1) * (k * q) + q^-1 * G ^+ 2) - k * s * (q * LOG q) =
    k * (s * q) + s * q * (q^-1 * G) ^+ 2.
  by move=> hq; field; rewrite gt_eqF.
rewrite er; exact: (e _ _ _ _ (hQ0 x)).
Qed.

(** Source for [dgpr_lemma31_heat_B2]: blueprint proof of lem:DGPR31 and
    DPGPR 2026, proof of Lemma 3.1: on Omega_T,
    H(rho |B|^2) = 2 rho |DB|^2 + 2 rho grad log q . grad |B|^2 +
    2 kappa rho |B|^2, from lem:heat_calculus(S), (product), (square) and
    (Bq), since S q = rho. Here lB and lQ are the values of D B_t(x) and
    D q_t(x), |DB|^2 is the sum of |D B_t(x)(eps_i)|^2, and
    grad |B_t|^2(x) . w = 2 B(t,x) . D B_t(x)(w). *)
Theorem dgpr_lemma31_heat_B2 (t : R) (x : X) (lB : X -> Hom X Y) (lQ : X -> R) : t < T ->
  dgpr_differential_values NH (fun z => B (t, z)) x lB ->
  @dgpr_differential_values R n R^o A1 (fun z => Q (t, z)) x lQ ->
  @dgpr_heat_operator R n R^o A1 (fun p : TX => (rho p * hom_inner BX hCY heX (B p) (B p) : R^o)) t x
    (2 * rho (t, x) * \sum_(i < n) hom_inner BX hCY heX (lB (eps i)) (lB (eps i)) +
     4 * rho (t, x) * hom_inner BX hCY heX (B (t, x)) (lB ((Q (t, x))^-1 *: dgpr_gradient_values lQ)) +
     2 * kappa (t, x) * rho (t, x) * hom_inner BX hCY heX (B (t, x)) (B (t, x))).
Proof.
move=> ht hlB hlQ.
have hS0 z : 0 < S (t, z) := dgpr_identities_S_pos hS z ht.
have hr0 z : 0 < rho (t, z) := dgpr_identities_rho_pos hS z ht.
have hQ0 z : 0 < Q (t, z) by rewrite /dgpr_heat_q divr_gt0.
have [hB hQ] := dgpr_heat_calculus_Bq hS x ht.
have hsq := dgpr_heat_calculus_square (hCZ := BH) hB hlB.
have [aB [DfB [D2B [jB _]]]] := hB.
have eB v : DfB x v = lB v := dgpr_differential_values_unique hNH (jB.2.1 x) hlB v.
have jsq := dgpr_heat_jet_inner_square (hCZ := BH) jB.
have hlf := jsq.2.1 x.
have hprod := dgpr_heat_calculus_product hA hsq hQ hlf hlQ.
have hSf := dgpr_heat_calculus_S hA ht hprod.
have hfg (p : TX) : p.1 < T ->
    S p *: (Q p *: (hom_inner BX hCY heX (B p) (B p) : R^o)) =
    (rho p * hom_inner BX hCY heX (B p) (B p) : R^o).
  case: p => r z /= hr; have hSz := dgpr_identities_S_pos hS z hr.
  change (S (r, z) * (Q (r, z) * hom_inner BX hCY heX (B (r, z)) (B (r, z))) =
    rho (r, z) * hom_inner BX hCY heX (B (r, z)) (B (r, z))).
  by rewrite mulrA /dgpr_heat_q mulrCA mulfV ?gt_eqF ?mulr1.
have hloc := dgpr_heat_operator_local ht hfg hSf.
have hval (h h' : R^o) : h = h' ->
    @dgpr_heat_operator R n R^o A1 (fun p : TX => (rho p * hom_inner BX hCY heX (B p) (B p) : R^o)) t x h ->
    @dgpr_heat_operator R n R^o A1 (fun p : TX => (rho p * hom_inner BX hCY heX (B p) (B p) : R^o)) t x h'.
  by move=> ->.
apply: (hval _ _ _ hloc).
rewrite (dgpr_values_scaleE (Q (t, x))^-1 _ hlB) eB.
rewrite [hom_inner _ _ _ _ (kappa (t, x) *: _)](bilZr (inner_bilinear BH)).
rewrite [hom_inner _ _ _ _ ((Q (t, x))^-1 *: _)](bilZr (inner_bilinear BH)).
have er : rho (t, x) = S (t, x) * Q (t, x).
  by rewrite /dgpr_heat_q mulrCA mulfV ?gt_eqF ?mulr1.
rewrite er.
have e (s q k b c w : R) : 0 < q ->
    s * (q * (2 * (k * b) + 2 * c) + k * q * b + 2 * (2 * w)) - k * s * (q * b) =
    2 * (s * q) * c + 4 * (s * q) * (q^-1 * w) + 2 * k * (s * q) * b.
  by move=> hq'; field; rewrite gt_eqF.
exact: (e _ _ _ _ _ _ (hQ0 x)).
Qed.

(** Source for [dgpr_lemma31_grad_log_rho]: blueprint proof of
    lem:DGPR31: grad log rho_t(x) = zeta(t,x) + grad log q_t(x) on
    Omega_T, since rho = S q (Federer 3.1.11, Leibniz formula); lQ and
    lr are the values of D q_t(x) and D rho_t(x). *)
Lemma dgpr_lemma31_grad_log_rho (t : R) (x : X) (lQ lr : X -> R) : t < T ->
  @dgpr_differential_values R n R^o A1 (fun z => Q (t, z)) x lQ ->
  @dgpr_differential_values R n R^o A1 (fun z => rho (t, z)) x lr ->
  (rho (t, x))^-1 *: dgpr_gradient_values lr = zeta (t, x) + (Q (t, x))^-1 *: dgpr_gradient_values lQ.
Proof.
move=> ht hlQ hlr.
have hS0 z : 0 < S (t, z) := dgpr_identities_S_pos hS z ht.
have hr0 z : 0 < rho (t, z) := dgpr_identities_rho_pos hS z ht.
have hQ0 z : 0 < Q (t, z) by rewrite /dgpr_heat_q divr_gt0.
have hSv := (dgpr_heat_S_jet hS x ht).2.1 x.
have hp := dgpr_values_scalar_product hA hSv hlQ.
have hp' : @dgpr_differential_values R n R^o A1 (fun z => rho (t, z)) x
    (fun v => dgpr_heat_S_first hS t x v *: (Q (t, x) : R^o) + S (t, x) *: (lQ v : R^o)).
  apply: (dgpr_values_ext _ _ hp) => // z.
  change (S (t, z) * (rho (t, z) / S (t, z)) = rho (t, z)).
  by rewrite mulrCA mulfV ?gt_eqF ?mulr1.
have el v : lr v = dgpr_heat_S_first hS t x v * Q (t, x) + S (t, x) * lQ v.
  exact: (dgpr_differential_values_unique hA hlr hp' v).
have er : rho (t, x) = S (t, x) * Q (t, x).
  by rewrite /dgpr_heat_q mulrCA mulfV ?gt_eqF ?mulr1.
rewrite /dgpr_heat_zeta /= /dgpr_gradient_values !scaler_sumr -big_split /=.
apply: eq_bigr => i _; rewrite el !scalerA -scalerDl; congr (_ *: _).
rewrite er; have hq := hQ0 x; have hs := hS0 x.
move: (S (t, x)) (Q (t, x)) hs hq (dgpr_heat_S_first hS t x (eps i)) (lQ (eps i)) => s0 q0 hs0 hq0 a0 b0.
by field; rewrite !gt_eqF.
Qed.

(** Source for [dgpr_lemma31_B_zeta_bound]: blueprint proof of
    lem:DGPR31: |B(zeta)| <= ||eta|| + sum_i |D B_t(x)(eps_i)| on
    Omega_T, by lem:identities(divB) with y = B(t,x)(zeta(t,x)) and the
    Cauchy-Schwarz inequality (Federer 1.7.1); lB are the values of
    D B_t(x). *)
Lemma dgpr_lemma31_B_zeta_bound (t : R) (x : X) (lB : X -> Hom X Y) : t < T ->
  dgpr_differential_values NH (fun z => B (t, z)) x lB ->
  NY (B (t, x) (zeta (t, x))) <= ND (eta (t, x)) + \sum_(i < n) NH (lB (eps i)).
Proof.
move=> ht hlB.
set y := B (t, x) (zeta (t, x)).
have hdiv := dgpr_identities_divB y ht hlB.
have hNy := inner_norm_nonnegative hCY y.
have hb0 : 0 <= ND (eta (t, x)) + \sum_(i < n) NH (lB (eps i)).
  by rewrite addr_ge0 ?inner_norm_nonnegative // sumr_ge0 // => i _; exact: inner_norm_nonnegative.
have [hy0|hy0] := eqVneq (NY y) 0; first by rewrite hy0.
have hpos : 0 < NY y by rewrite lt0r hy0 hNy.
have h1 : NY y ^+ 2 <= (ND (eta (t, x)) + \sum_(i < n) NH (lB (eps i))) * NY y.
  rewrite (inner_norm_sqr hCY).
  have -> : CY y y = eta (t, x) y - \sum_(i < n) CY (lB (eps i) (eps i)) y by rewrite -hdiv addrC addKr.
  rewrite mulrDl; apply: lerD.
  - have h := hom_norm_vector_bound hCY (scalar_inner_productP R) heY (eta (t, x)) y.
    rewrite scalar_inner_normE in h; exact: le_trans (ler_norm _) h.
  - rewrite -sumrN mulr_suml; apply: ler_sum => i _.
    apply: le_trans (ler_norm _) _; rewrite normrN.
    apply: le_trans (inner_cauchy hCY _ _) _.
    by apply: ler_wpM2r => //; exact: (dgpr_hom_apply_bound hCY (lB (eps i)) i).
by rewrite expr2 ler_pM2r in h1.
Qed.

(** Source for [dgpr_lemma31_B_gradient_bound]: blueprint proof of
    lem:DGPR31: on Omega_T,
    |B(grad log rho)|^2 <= 4 ||eta||^2 + 4 n |DB|^2 + 2 Lambda^2 |grad log q|^2,
    from B(grad log rho) = B(zeta) + B(grad log q), |B| <= Lambda
    (lem:identities(bounds)) and [dgpr_lemma31_B_zeta_bound]; here
    |DB|^2 is the sum of |D B_t(x)(eps_i)|^2. *)
Theorem dgpr_lemma31_B_gradient_bound (t : R) (x : X) (lB : X -> Hom X Y) (lQ lr : X -> R) : t < T ->
  dgpr_differential_values NH (fun z => B (t, z)) x lB ->
  @dgpr_differential_values R n R^o A1 (fun z => Q (t, z)) x lQ ->
  @dgpr_differential_values R n R^o A1 (fun z => rho (t, z)) x lr ->
  NY (B (t, x) ((rho (t, x))^-1 *: dgpr_gradient_values lr)) ^+ 2 <=
    4 * ND (eta (t, x)) ^+ 2 + 4 * n%:R * \sum_(i < n) NH (lB (eps i)) ^+ 2 +
    2 * Lam ^+ 2 * N ((Q (t, x))^-1 *: dgpr_gradient_values lQ) ^+ 2.
Proof.
move=> ht hlB hlQ hlr.
rewrite (dgpr_lemma31_grad_log_rho ht hlQ hlr) linearD.
set w := (Q (t, x))^-1 *: dgpr_gradient_values lQ.
have hz := dgpr_lemma31_B_zeta_bound ht hlB.
have [_ _ _ hBL _] := dgpr_identities_bounds hS x ht.
have hw : NY (B (t, x) w) <= Lam * N w.
  apply: le_trans (hom_norm_vector_bound BX hCY heX (B (t, x)) w) _.
  by apply: ler_wpM2r; [exact: inner_norm_nonnegative | exact: hBL].
have hNz := inner_norm_nonnegative hCY (B (t, x) (zeta (t, x))).
have hNw := inner_norm_nonnegative hCY (B (t, x) w).
have hNe : 0 <= ND (eta (t, x)) := inner_norm_nonnegative BD (eta (t, x)).
have hNww := inner_norm_nonnegative BX w.
have hL0 : 0 <= Lam := ltW (dgpr_standing_Lambda hS).
have hc0 : 0 <= \sum_(i < n) NH (lB (eps i)) by apply: sumr_ge0 => i _; exact: inner_norm_nonnegative.
have hcs := dgpr_sum_sqr_le (fun i : 'I_n => NH (lB (eps i))).
have ht1 := inner_norm_triangle hCY (B (t, x) (zeta (t, x))) (B (t, x) w).
have hT0 := inner_norm_nonnegative hCY (B (t, x) (zeta (t, x)) + B (t, x) w).
move: hz hw ht1 hcs hT0 hNz hNw hNe hNww hc0.
move: (NY (B (t, x) (zeta (t, x)) + B (t, x) w)) (NY (B (t, x) (zeta (t, x)))) (NY (B (t, x) w)).
move: (ND (eta (t, x))) (\sum_(i < n) NH (lB (eps i))) (\sum_(i < n) NH (lB (eps i)) ^+ 2) (N w).
move=> e c c2 nw a z b hz hw ht1 hcs ha0 hz0 hb0 he0 hnw0 hc0.
have h1 : a ^+ 2 <= (z + b) ^+ 2 by apply: lerXn2r; rewrite ?nnegrE ?addr_ge0.
have h2 : z ^+ 2 <= (e + c) ^+ 2 by apply: lerXn2r; rewrite ?nnegrE ?addr_ge0.
have h3 : b ^+ 2 <= (Lam * nw) ^+ 2 by apply: lerXn2r; rewrite ?nnegrE ?mulr_ge0.
have h4 : (z + b) ^+ 2 <= 2 * z ^+ 2 + 2 * b ^+ 2 by have := sqr_ge0 (z - b); nra.
have h5 : (e + c) ^+ 2 <= 2 * e ^+ 2 + 2 * c ^+ 2 by have := sqr_ge0 (e - c); nra.
rewrite exprMn in h3; nra.
Qed.

(** Source for [dgpr_lemma31_eta_bound]: blueprint proof of lem:DGPR31,
    (eq:31:eta), pointwise form: on Omega_T, if rho <= U, then
    rho ||eta||^2 <= (T - t)^(-1) rho and
    rho ||eta||^2 <= S^(-1) ||Psi||^2 <= (S^(-1) R) R <= (T - t)^(-1/2) R,
    by lem:identities(div) and (bounds). The hypothesis rho <= U is
    lem:identities(bounds). *)
Lemma dgpr_lemma31_eta_bound (t : R) (x : X) : t < T -> rho (t, x) <= U (t, x) ->
  (rho (t, x) * ND (eta (t, x)) ^+ 2 <= rho (t, x) / (T - t)) /\
  (rho (t, x) * ND (eta (t, x)) ^+ 2 <= Rr (t, x) / Num.sqrt (T - t)).
Proof.
move=> ht hrU.
have hs : 0 < T - t by rewrite subr_gt0.
have hq : 0 < Num.sqrt (T - t) by rewrite sqrtr_gt0.
have hS0 := dgpr_identities_S_pos hS x ht.
have hr0 := dgpr_identities_rho_pos hS x ht.
have hR0 := dgpr_identities_R_ge0 hS x ht.
have hUS := dgpr_identities_U_le_S hS x ht.
have hU0 := dgpr_identities_U_pos hS x ht.
have hPsi := dgpr_identities_Psi_bound hS x ht.
have he := dgpr_identities_eta_bound hS x ht.
have hE0 : 0 <= ND (eta (t, x)) := inner_norm_nonnegative BD (eta (t, x)).
have hP0 : 0 <= ND (Psi (t, x)) := inner_norm_nonnegative BD (Psi (t, x)).
have eE : ND (eta (t, x)) = (S (t, x))^-1 * ND (Psi (t, x)).
  by rewrite /dgpr_heat_eta /= /hom_norm (real_seminorm_scale hND.1) gtr0_norm ?invr_gt0.
have hSR : Num.sqrt (T - t) * Rr (t, x) <= S (t, x).
  by rewrite /dgpr_heat_S /= lerDr ltW.
split.
- have h2 : ND (eta (t, x)) ^+ 2 <= ((Num.sqrt (T - t))^-1) ^+ 2.
    by apply: lerXn2r; rewrite ?nnegrE ?invr_ge0 ?sqrtr_ge0.
  have e2 : ((Num.sqrt (T - t))^-1) ^+ 2 = (T - t)^-1 by rewrite exprVn sqr_sqrtr // ltW.
  rewrite e2 in h2; exact: (ler_wpM2l (ltW hr0) h2).
- have hrS : rho (t, x) <= S (t, x) := le_trans hrU hUS.
  rewrite eE; move: (S (t, x)) hS0 hrS hSR (ND (Psi (t, x))) hP0 hPsi => s hs0 hrs hsr P hP hPR.
  move: (rho (t, x)) hr0 hrs (Rr (t, x)) hR0 hsr hPR => r hr hrs Rv hRv hsr hPR.
  move: (Num.sqrt (T - t)) hq hsr => w hw hsr.
  have h1 : r * (s^-1 * P) ^+ 2 <= s * (s^-1 * P) ^+ 2 := ler_wpM2r (sqr_ge0 _) hrs.
  apply: le_trans h1 _.
  have e1 : s * (s^-1 * P) ^+ 2 = s^-1 * P ^+ 2 by field; rewrite gt_eqF.
  rewrite e1.
  have hP2 : P ^+ 2 <= Rv ^+ 2 by apply: lerXn2r; rewrite ?nnegrE.
  have hsi : 0 <= s^-1 by rewrite invr_ge0 ltW.
  apply: le_trans (ler_wpM2l hsi hP2) _.
  have e3 : s^-1 * Rv = (s^-1 * w^-1) * (w * Rv) by field; rewrite !gt_eqF.
  have hsw : 0 <= s^-1 * w^-1 by rewrite mulr_ge0 // invr_ge0 ltW.
  have h4 : s^-1 * Rv <= w^-1.
    rewrite e3; apply: le_trans (ler_wpM2l hsw hsr) _.
    by rewrite mulrAC mulVf ?gt_eqF ?mul1r.
  have e4 : s^-1 * Rv ^+ 2 = Rv * (s^-1 * Rv) by rewrite expr2 mulrCA.
  rewrite e4; exact: (ler_wpM2l hRv h4).
Qed.

(** Source for [dgpr_lemma31_eta_pointwise]: blueprint proof of
    lem:DGPR31, (eq:31:eta), pointwise form on Omega_T:
    rho ||eta||^2 <= min{(T - t)^(-1) rho, (T - t)^(-1/2) R}, by
    [dgpr_lemma31_eta_bound] and rho <= U (lem:identities(bounds)). *)
Theorem dgpr_lemma31_eta_pointwise (t : R) (x : X) : t < T ->
  (rho (t, x) * ND (eta (t, x)) ^+ 2 <= rho (t, x) / (T - t)) /\
  (rho (t, x) * ND (eta (t, x)) ^+ 2 <= Rr (t, x) / Num.sqrt (T - t)).
Proof. move=> ht; exact: (dgpr_lemma31_eta_bound ht (dgpr_identities_rho_le_U hS x ht)). Qed.

End Lemma31Pointwise.
