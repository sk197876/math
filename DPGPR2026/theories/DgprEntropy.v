(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 4, the
    entropy of the heated measure; blueprint dgpr_blueprint.tex,
    def:entropy and lem:entropy.

    Assume (S) ([dgpr_standing]). For t < T,
      H(ρ_t) = ∫ ρ_t log ρ_t dL^n,
      H̃(ρ_t) = H(ρ_t) + 2^(-1) (n − m) γ log(T − t).
    The entropy H(ρ_t) is the upper integral of Federer 2.4.2, taken as a real number
    ([fine]); for t < T the function ρ_t log ρ_t is L^n summable and the
    upper integral is its integral ([dgpr_entropy_derivative]).

    By lem:entropy, [t ↦ H(ρ_t)] is of class 1 on R ∩ {t : t < T} with
    derivative [t ↦ I(ρ_t)], and H(ρ_0) ≤ γ log γ − 2^(-1) n γ log(4πT).
    The proof is that of the blueprint. On Ω_T,
      H(ρ log ρ) = ρ |grad log ρ|²,
    by the chain rule for the jets of ρ (DgprHeatJetCalculus.v) and
    H ρ = 0 (lem:identities(heat)); the time derivative of ∫ ρ_t log ρ_t
    is then ∫ H(ρ log ρ)_t by DgprHeatIntegral.v (lem:classes(cl:dt),
    (cl:div)). The bound of H(ρ_0) follows from ρ_0 ≤ γ (4πT)^(-n/2)
    (lem:kernel(6)) and the monotonicity of the logarithm.

    The results [dgpr_entropy_derivative_of] and
    [dgpr_entropy_initial_bound_of] assume the Gaussian decay before T of
    ρ log ρ (hypothesis [hG]). This follows from lem:regularity (log ρ
    has polynomial growth before T, ρ has Gaussian decay before T) and
    lem:classes(cl:product) ([dgpr_entropy_gaussian]), which gives
    [dgpr_entropy_derivative] and [dgpr_entropy_initial_bound]. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LinearBasis HomInner ScalarInnerProduct
  ProductInner PartialFunctionUP MeasureUP MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  SummableRealFunctionUP SummableRealArithmetic RadonMeasureUP EuclideanLebesgueDimensions
  ScalarNormMetricCompleteness LocalUniquenessExample NormDifferentialUP NormDifferentialLocal
  NormClassOneUP NormRegularity SmoothFunctionSpaceUP SmoothTestSpaces
  RealExponentialUP RealExponentialSealed RealExponentialLaws.
From DPGPR Require Import DgprHeatKernel DgprHeatExtension DgprHeatSemiconvex DgprDifferentialCalculus
  DgprHeatJets DgprHeatJetCalculus DgprBackwardHeat DgprStanding DgprHeatObjects DgprIdentities
  DgprHeatCalculus DgprIdentitiesSmooth DgprMeasureComparison DgprLemma31 DgprLemma31Main
  DgprGrowthClasses DgprParameterIntegralSmooth DgprHeatIntegral DgprTimeIntegrals DgprClassesProduct
  DgprRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section LogarithmPowers.
Variable R : realType.
Local Notation LOG := (@RealExponential.logarithm R).

(** Source for [dgpr_logarithm_natural_power]: log(a^k) = k log a for
    0 < a, from log(a b) = log a + log b (Federer 2.4.12, p. 86);
    supporting lem:entropy. *)
Lemma dgpr_logarithm_natural_power (a : R) (k : nat) : 0 < a -> LOG (a ^+ k) = k%:R * LOG a.
Proof.
move=> ha; elim: k => [|k ih]; first by rewrite expr0 mul0r real_logarithm_one.
by rewrite exprS real_logarithm_product ?exprn_gt0 // ih -addn1 natrD mulrDl mul1r addrC.
Qed.

(** Source for [dgpr_logarithm_sqrt]: log(a^(1/2)) = 2^(-1) log a for
    0 < a; supporting lem:entropy. *)
Lemma dgpr_logarithm_sqrt (a : R) : 0 < a -> LOG (Num.sqrt a) = 2^-1 * LOG a.
Proof.
move=> ha; have hs : 0 < Num.sqrt a by rewrite sqrtr_gt0.
have e : LOG a = 2 * LOG (Num.sqrt a).
  by rewrite -{1}(sqr_sqrtr (ltW ha)) expr2 real_logarithm_product // mulr2n mulrDl mul1r.
by rewrite e; field.
Qed.

(** Source for [dgpr_logarithm_kernel_constant]: log((4πs)^(-n/2)) =
    −2^(-1) n log(4πs) for 0 < s, the factor of p_s (lem:kernel(6));
    supporting lem:entropy. *)
Lemma dgpr_logarithm_kernel_constant (n : nat) (s : R) : 0 < s ->
  LOG (Num.sqrt (4 * dgpr_pi R * s) ^- n) = - (2^-1 * n%:R * LOG (4 * dgpr_pi R * s)).
Proof.
move=> hs; have hpi : 0 < dgpr_pi R := @dgpr_pi_gt0 R.
have ha : 0 < 4 * dgpr_pi R * s by rewrite mulr_gt0 // mulr_gt0.
have hq : 0 < Num.sqrt (4 * dgpr_pi R * s) by rewrite sqrtr_gt0.
rewrite real_logarithm_inverse ?exprn_gt0 // dgpr_logarithm_natural_power // dgpr_logarithm_sqrt //.
by congr (- _); ring.
Qed.
End LogarithmPowers.

Section ClassOneAgreement.
Variable R : realType.
Local Notation NR := (fun t : R^o => `|t|).
Local Notation hNR := (@scalar_absolute_value_norm R).

(** Source for [dgpr_class_one_field_agreement]: Federer 3.1.1, p. 210,
    and 3.1.11, p. 223: the class 1 conditions on A concern only the
    values of f and of the field of differentials at points of A;
    supporting lem:entropy. *)
Lemma dgpr_class_one_field_agreement (A : set R) (f g : R -> R) (D D' : R -> Hom R^o R^o) :
  (forall t, A t -> f t = g t) -> (forall t, A t -> D t = D' t) ->
  is_norm_class_one_field NR NR A f D -> is_norm_class_one_field NR NR A g D'.
Proof.
move=> hfg hD [h0 h1 h2]; split.
- move=> a ha; have [hi hc] := h0 a ha; split => // e he.
  have [d [hd hb]] := hc e he; exists d; split => // h hh hn.
  by rewrite -(hfg _ hh) -(hfg _ ha); exact: hb.
- move=> a ha; rewrite -(hD a ha).
  exact: (@norm_differential_domain_agreement R R^o R^o (fun t : R^o => `|t|) (fun t : R^o => `|t|) hNR A f g a (D a) (fun t ht => hfg t ht) (h1 a ha)).
- move=> a ha e he; have [d [hd hb]] := h2 a ha e he; exists d; split => // h hh hn v.
  by rewrite -(hD _ hh) -(hD _ ha); exact: hb.
Qed.
End ClassOneAgreement.

Section Entropy.
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
Local Notation hZ1 := (@scalar_norm_metric_complete R).
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
Local Notation hmu0 := (dgpr_standing_mu0_measure hS).
Local Notation hOmu0 := (dgpr_standing_mu0_borel hS).
Local Notation hMmu0 := (dgpr_standing_mu0_mass hS).
Local Notation LL := (@euclidean_lebesgue_measure R n).
Local Notation hLL := (euclidean_lebesgue_is_measure R n).
Local Notation rho := (dgpr_heat_rho hS).
Local Notation LOG := (@RealExponential.logarithm R).

(** Source for [dgpr_entropy]: DPGPR 2026, section 4, and blueprint
    def:entropy: H(ρ_t) = ∫ ρ_t log ρ_t dL^n, the upper integral of
    Federer 2.4.2 as a real number; it is the integral for t < T
    ([dgpr_entropy_derivative]). *)
Definition dgpr_entropy (t : R) : R :=
  fine (measure_upper_integral LL (real_total_integrand (fun x => rho (t, x) * LOG (rho (t, x))))).

(** Source for [dgpr_entropy_tilde]: DPGPR 2026, section 4, and blueprint
    def:entropy: H̃(ρ_t) = H(ρ_t) + 2^(-1) (n − m) γ log(T − t). *)
Definition dgpr_entropy_tilde (t : R) : R :=
  dgpr_entropy t + 2^-1 * (n - m)%:R * gamma * LOG (T - t).

(** Source for [dgpr_entropy_heat]: blueprint proof of lem:entropy:
    H(ρ log ρ) = ρ |grad log ρ|² on Ω_T. With Φ(r) = r log r, the chain
    rule gives H(Φ ∘ ρ) = Φ'(ρ) H ρ + Φ''(ρ) |grad ρ|² (Federer 3.1.1(3),
    3.1.11), and H ρ = 0 by lem:identities(heat). *)
Lemma dgpr_entropy_heat (t : R) (x : X) : t < T ->
  @dgpr_heat_operator R n R^o A1 (fun q : TX => rho q * LOG (rho q)) t x
    (rho (t, x) * N (dgpr_heat_grad_log_rho hS (t, x)) ^+ 2).
Proof.
move=> ht.
have hr0 z : 0 < rho (t, z) := dgpr_identities_rho_pos hS z ht.
have [_ _ _ _ [a [Dr [D2 [jr e0]]]]] := dgpr_identities_heat_extensions hS x ht.
have hc := dgpr_heat_jet_compose (@dgpr_entropy_curve1 R) (@dgpr_entropy_curve2 R) hr0 jr.
exists ((LOG (rho (t, x)) + 1) * a), (fun y v => (LOG (rho (t, y)) + 1) * Dr y v),
  (fun v w => (rho (t, x))^-1 * Dr x v * Dr x w + (LOG (rho (t, x)) + 1) * D2 v w).
split; first exact: hc.
have [_ [hDr _]] := jr.
have eD v : Dr x v = dgpr_heat_rho_first hS t x v.
  exact: (dgpr_differential_values_unique hA (hDr x) (dgpr_lemma31_rho_first hS x ht)).
rewrite /dgpr_heat_grad_log_rho (real_seminorm_scale hN.1) gtr0_norm ?invr_gt0 //.
rewrite exprMn (dgpr_gradient_norm_sqr (dgpr_lemma31_rho_first hS x ht)).
rewrite /dgpr_laplacian_values big_split /= -mulr_sumr.
move: e0; rewrite /dgpr_laplacian_values => e0.
have -> : \sum_(i < n) (rho (t, x))^-1 * Dr x (eps i) * Dr x (eps i) =
    (rho (t, x))^-1 * \sum_(i < n) dgpr_heat_rho_first hS t x (eps i) ^+ 2.
  by rewrite mulr_sumr; apply: eq_bigr => i _; rewrite eD expr2 mulrA.
have ea : a = - \sum_(i < n) D2 (eps i) (eps i).
  by apply/eqP; rewrite -addr_eq0 -e0.
rewrite ea.
set s := \sum_(i < n) _ ^+ 2; set l := \sum_(i < n) D2 _ _.
have hr := hr0 x; move: hr; set r := rho (t, x) => hr.
by field; rewrite gt_eqF.
Qed.

(** Source for [dgpr_entropy_kernel_bound]: blueprint proof of
    lem:entropy: ρ_t ≤ γ (4π(T − t))^(-n/2) for t < T, by lem:kernel(6)
    and ∫ 1 dμ_0 = γ (Federer 2.4.4). *)
Lemma dgpr_entropy_kernel_bound (t : R) (x : X) : t < T ->
  rho (t, x) <= dgpr_kernel_constant n (T - t) * gamma.
Proof.
move=> ht; have hs : 0 < T - t by rewrite subr_gt0.
have h := dgpr_one_integral hmu0 hOmu0 hMmu0 x (dgpr_kernel_class_zero hs)
  (fun z => dgpr_kernel_abs_le z hs).
have hc := dgpr_constant_integral hmu0 hMmu0 (dgpr_kernel_constant n (T - t)).
exact: (dgpr_integral_le hmu0 (fun y => dgpr_kernel_max (x - y) hs) h hc).
Qed.

(** Source for [dgpr_entropy_integral_of]: the upper integral of
    Federer 2.4.2 of a summable function is its integral; hence
    H(ρ_t) = a whenever a is the integral of ρ_t log ρ_t. *)
Lemma dgpr_entropy_integral_of (t a : R) :
  is_measure_integral LL (real_total_integrand (fun x => rho (t, x) * LOG (rho (t, x)))) a%:E ->
  dgpr_entropy t = a.
Proof.
move=> ha; rewrite /dgpr_entropy.
by rewrite (@measure_upper_integral_unique R X LL _ _ a%:E (measure_upper_integral_specification LL _) ha.2.1).
Qed.

(** Source for [dgpr_fisher_information_of]: the upper integral
    I(ρ_t) of Federer 2.4.2 is the integral a whenever the latter
    exists; supporting lem:entropy. *)
Lemma dgpr_fisher_information_of (t a : R) :
  is_measure_integral LL (real_total_integrand (fun x => rho (t, x) * N (dgpr_heat_grad_log_rho hS (t, x)) ^+ 2))
    a%:E ->
  dgpr_fisher_information hS t = a%:E.
Proof.
move=> ha; rewrite /dgpr_fisher_information.
exact: (@measure_upper_integral_unique R X LL _ _ a%:E (measure_upper_integral_specification LL _) ha.2.1).
Qed.

Section EntropyConditional.
Hypothesis hG : dgpr_gaussian_decay_before hA T (fun q : TX => rho q * LOG (rho q)).

(** Source for [dgpr_entropy_derivative_of]: blueprint lem:entropy, first
    assertion, under the hypothesis [hG]: for t < T, ρ_t log ρ_t and
    ρ_t |grad log ρ_t|² are L^n summable with integrals H(ρ_t) and I(ρ_t),
    and [t ↦ H(ρ_t)] is of class 1 on R ∩ {t : t < T} with derivative
    [t ↦ I(ρ_t)] (DgprHeatIntegral.v). *)
Theorem dgpr_entropy_derivative_of :
  [/\ forall t, t < T ->
        is_measure_integral LL (real_total_integrand (fun x => rho (t, x) * LOG (rho (t, x))))
          (dgpr_entropy t)%:E,
      forall t, t < T ->
        is_measure_integral LL
          (real_total_integrand (fun x => rho (t, x) * N (dgpr_heat_grad_log_rho hS (t, x)) ^+ 2))
          (fine (dgpr_fisher_information hS t))%:E &
      is_norm_class_one_field A1 A1 [set t : R | t < T]%classic dgpr_entropy
        (fun t => dgpr_line_hom (fine (dgpr_fisher_information hS t) : R^o))].
Proof.
have hH := fun t x (ht : t < T) => dgpr_entropy_heat x ht.
have [I [H [hI hHi hc]]] := @dgpr_heat_integral R n T _
  (fun q : TX => rho q * N (dgpr_heat_grad_log_rho hS q) ^+ 2) hG hH.
have eI t : t < T -> dgpr_entropy t = I t by move=> ht; exact: dgpr_entropy_integral_of (hI t ht).
have eH t : t < T -> fine (dgpr_fisher_information hS t) = H t.
  by move=> ht; rewrite (dgpr_fisher_information_of (hHi t ht)).
split.
- by move=> t ht; rewrite (eI t ht); exact: hI.
- by move=> t ht; rewrite (eH t ht); exact: hHi.
apply: (dgpr_class_one_field_agreement _ _ hc) => t ht; first by rewrite eI.
by rewrite (eH t ht).
Qed.

(** Source for [dgpr_entropy_initial_bound_of]: blueprint lem:entropy,
    second assertion, under the hypothesis [hG]:
    H(ρ_0) ≤ γ log γ − 2^(-1) n γ log(4πT). By lem:kernel(6),
    ρ_0 ≤ γ (4πT)^(-n/2), hence ρ_0 log ρ_0 ≤ ρ_0 log(γ (4πT)^(-n/2)), and
    ∫ ρ_0 dL^n = γ by lem:identities(mass). *)
Theorem dgpr_entropy_initial_bound_of :
  dgpr_entropy 0 <= gamma * LOG gamma - 2^-1 * n%:R * gamma * LOG (4 * dgpr_pi R * T).
Proof.
have hT := dgpr_standing_T hS.
have hg := dgpr_standing_gamma hS.
have [hI _ _] := dgpr_entropy_derivative_of.
have [_ _ _ hmass] := dgpr_identities_mass hS hT.
have hc : 0 < dgpr_kernel_constant n (T - 0) * gamma.
  rewrite subr0 mulr_gt0 // /dgpr_kernel_constant invr_gt0 exprn_gt0 // sqrtr_gt0.
  by rewrite mulr_gt0 // mulr_gt0 // (@dgpr_pi_gt0 R).
have hle x : rho (0, x) * LOG (rho (0, x)) <= LOG (dgpr_kernel_constant n (T - 0) * gamma) * rho (0, x).
  have hr := dgpr_identities_rho_pos hS x hT.
  rewrite mulrC; apply: ler_wpM2r; first exact: ltW.
  by rewrite real_logarithm_order //; exact: dgpr_entropy_kernel_bound.
have h2 := real_total_integral_scale hLL (LOG (dgpr_kernel_constant n (T - 0) * gamma)) hmass.
have hb := dgpr_integral_le hLL hle (hI 0 hT) h2.
apply: le_trans hb _.
rewrite subr0 real_logarithm_product // ?dgpr_logarithm_kernel_constant //.
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
rewrite /dgpr_kernel_constant invr_gt0 exprn_gt0 // sqrtr_gt0.
by rewrite mulr_gt0 // mulr_gt0 // (@dgpr_pi_gt0 R).
Qed.
End EntropyConditional.

(** Source for [dgpr_entropy_gaussian]: blueprint proof of lem:entropy:
    ρ log ρ has Gaussian decay before T, by lem:regularity (log ρ has
    polynomial growth before T, ρ has Gaussian decay before T) and
    lem:classes(cl:product). *)
Lemma dgpr_entropy_gaussian : dgpr_gaussian_decay_before hA T (fun q : TX => rho q * LOG (rho q)).
Proof.
have [_ hlr _] := dgpr_regularity_log_polynomial hS.
have [_ _ _ _ hr] := dgpr_regularity_gaussian_extensions hS.
exact: (dgpr_classes_product_gaussian_before hA (dgpr_scalar_mul_flip_bilinear R) hlr hr).
Qed.

(** Source for [dgpr_entropy_derivative]: DPGPR 2026, section 4, and
    blueprint lem:entropy, first assertion: for t < T, ρ_t log ρ_t and
    ρ_t |grad log ρ_t|² are L^n summable with integrals H(ρ_t) and I(ρ_t),
    and [t ↦ H(ρ_t)] is of class 1 on R ∩ {t : t < T} with derivative
    [t ↦ I(ρ_t)]. *)
Theorem dgpr_entropy_derivative :
  [/\ forall t, t < T ->
        is_measure_integral LL (real_total_integrand (fun x => rho (t, x) * LOG (rho (t, x))))
          (dgpr_entropy t)%:E,
      forall t, t < T ->
        is_measure_integral LL
          (real_total_integrand (fun x => rho (t, x) * N (dgpr_heat_grad_log_rho hS (t, x)) ^+ 2))
          (fine (dgpr_fisher_information hS t))%:E &
      is_norm_class_one_field A1 A1 [set t : R | t < T]%classic dgpr_entropy
        (fun t => dgpr_line_hom (fine (dgpr_fisher_information hS t) : R^o))].
Proof. exact: (dgpr_entropy_derivative_of dgpr_entropy_gaussian). Qed.

(** Source for [dgpr_entropy_initial_bound]: DPGPR 2026, section 4, and
    blueprint lem:entropy, second assertion:
    H(ρ_0) ≤ γ log γ − 2^(-1) n γ log(4πT). *)
Theorem dgpr_entropy_initial_bound :
  dgpr_entropy 0 <= gamma * LOG gamma - 2^-1 * n%:R * gamma * LOG (4 * dgpr_pi R * T).
Proof. exact: (dgpr_entropy_initial_bound_of dgpr_entropy_gaussian). Qed.

End Entropy.
