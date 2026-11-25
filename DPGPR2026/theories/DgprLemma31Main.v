(** De Philippis, Gennaioli, Pigati and Rindler (2026), proof of
    Lemma 3.1; blueprint dgpr_blueprint.tex, proof of lem:DGPR31: the
    estimates at a fixed time t < T. With J(t) = ∫ rho_t log q_t dL^n and
    K(t) = ∫ rho_t |B_t|^2 dL^n, the maps h_J = H(rho log q) and
    h_K = H(rho |B|^2) of DgprLemma31.v have L^n summable sections, J and
    K are of class 1 with derivatives ∫ h_J and ∫ h_K
    (DgprHeatIntegral.v), and the integrand
    rho (|DB|^2 + |B(grad log rho)|^2) is bounded pointwise by
    (1 + 4n) h_K + (16 n + 6) Lambda^2 h_J + 4 min{(T-t)^(-1) rho, (T-t)^(-1/2) R}.

    The Gaussian decay before T of rho log q and of rho |B|^2
    (lem:regularity with lem:classes(cl:product)) enters as the
    hypotheses [hJgauss] and [hKgauss] of the section. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm InnerNormInequalities
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  LinearBasis HomInner HomInnerCoordinates OrthonormalFamilies EuclideanStiefelInnerSplitting
  ScalarInnerProduct ProductInner TensorUP Bilinear CompleteMetricUP PartialFunctionUP PartialFunctionBasic
  PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralComparison MeasureIntegralUniqueness MeasureUpperIntegralMonotone
  SummableRealFunctionUP SummableRealArithmetic RadonMeasureUP EuclideanLebesgueDimensions
  ScalarNormMetricCompleteness LocalUniquenessExample
  NormDifferentialUP NormClassOneUP NormRegularity SmoothFunctionSpaceUP SmoothTestSpaces
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearOne
  RealExponentialUP RealExponentialSealed HomNormBound.
From DPGPR Require Import DgprOrthonormalCoordinates DgprHomNorms DgprHeatKernel DgprHeatExtension
  DgprDifferentialCalculus DgprHeatJets DgprBackwardHeat DgprStanding DgprHeatObjects DgprIdentities
  DgprFunctionals DgprHeatJetCalculus DgprHeatCalculus DgprIdentitiesDivergence DgprIdentitiesSmooth
  DgprMeasureComparison DgprLemma31 DgprGrowthClasses DgprIntegrationByPartsClasses DgprHeatIntegral
  DgprHeatSemiconvex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section IntegralComparison.
Variable R : realType.
Variable X : choiceType.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.

(** Source for [dgpr_pointwise_le_locus]: a pointwise inequality between
    real functions holds mu almost everywhere (Federer 2.4.4(5), p. 82,
    hypothesis form). *)
Lemma dgpr_pointwise_le_locus (f g : X -> R) : (forall x, f x <= g x) ->
  measure_almost_everywhere mu (partial_extended_le_locus (real_total_integrand f) (real_total_integrand g)).
Proof.
move=> hfg.
apply: (@measure_almost_everywhere_mono R _ mu hm setT _ _ (measure_almost_everywhere_true hm)) => x _.
exists (f x)%:E, (g x)%:E; split; first exact/real_total_integrand_graph.
by split; [exact/real_total_integrand_graph | rewrite lee_fin].
Qed.

(** Source for [dgpr_integral_le]: Federer 2.4.4(5), p. 82: if f <= g
    and both are summable, then ∫ f <= ∫ g. *)
Lemma dgpr_integral_le (f g : X -> R) (a b : R) : (forall x, f x <= g x) ->
  is_measure_integral mu (real_total_integrand f) a%:E ->
  is_measure_integral mu (real_total_integrand g) b%:E -> a <= b.
Proof.
move=> hfg ha hb.
by have := measure_integral_monotone hm ha hb (dgpr_pointwise_le_locus hfg); rewrite lee_fin.
Qed.

(** Source for [dgpr_integral_ge0]: Federer 2.4.4(5), p. 82, with
    the function 0 = 0 f of integral 0. *)
Lemma dgpr_integral_ge0 (f : X -> R) (a : R) : (forall x, 0 <= f x) ->
  is_measure_integral mu (real_total_integrand f) a%:E -> 0 <= a.
Proof.
move=> hf ha.
have h0 := real_total_integral_scale hm 0 ha; rewrite mul0r in h0.
apply: (dgpr_integral_le _ h0 ha) => x; rewrite mul0r; exact: hf.
Qed.

(** Source for [dgpr_upper_integral_le]: Federer 2.4.2-2.4.4, pp. 81-82:
    if f <= g and g is summable with integral b, then the upper integral
    of f is at most b. *)
Lemma dgpr_upper_integral_le (f g : X -> R) (b : R) : (forall x, f x <= g x) ->
  is_measure_integral mu (real_total_integrand g) b%:E ->
  (measure_upper_integral mu (real_total_integrand f) <= b%:E)%E.
Proof.
move=> hfg hb.
have hmono := measure_upper_integral_monotone hm (dgpr_pointwise_le_locus hfg).
have eg := @measure_upper_integral_unique R X mu (real_total_integrand g) _ b%:E
  (measure_upper_integral_specification mu _) hb.2.1.
by rewrite eg in hmono.
Qed.
End IntegralComparison.

Section Lemma31Integrals.
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
Local Notation HI := (hom_inner BX hCY heX).
Local Notation BD := (hom_inner_productP hCY (scalar_inner_productP R) heY).
Local Notation ND := (hom_norm hCY (scalar_inner_productP R) heY).
Local Notation hND := (inner_norm_real_norm BD).
Local Notation hZ1 := (@scalar_norm_metric_complete R).
Local Notation hsep1 := (scalar_norm_separable R).
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
Local Notation one := (fun _ : X => (1 : R^o)).
Local Notation LL := (@euclidean_lebesgue_measure R n).
Local Notation hLL := (euclidean_lebesgue_is_measure R n).
Local Notation W := (dgpr_heat_W hS).
Local Notation S := (dgpr_heat_S hS).
Local Notation B := (dgpr_heat_B hS).
Local Notation eta := (dgpr_heat_eta hS).
Local Notation U := (dgpr_heat_U hS).
Local Notation Rr := (dgpr_heat_R hS).
Local Notation rho := (dgpr_heat_rho hS).
Local Notation kappa := (dgpr_heat_kappa hS).
Local Notation Q := (dgpr_heat_q hS).
Local Notation LOG := (@RealExponential.logarithm R).
Local Notation lawss k := (@ContinuousMultilinear.laws R k X R^o N A1 hN hA).

(** Source for [dgpr_lemma31_q_values_exist]: q_t is differentiable at
    every point for t < T, since q is of class infinity on Omega_T
    (lem:regularity) and so is its section (Federer 3.1.11). *)
Lemma dgpr_lemma31_q_values_exist (p : TX) : exists l : X -> R,
  p.1 < T -> @dgpr_differential_values R n R^o A1 (fun z => Q (p.1, z)) p.2 l.
Proof.
case: (pselect (p.1 < T)) => ht; last by exists (fun _ => 0).
have [_ _ _ hQc] := dgpr_regularity_smooth hS.
have [_ [D1 [hD1 _]]] := dgpr_slice_class ht (hQc 1%N).
exists (continuous_multilinear_one_operator (lawss 1) (D1 p.2)) => _.
exists (continuous_multilinear_one_operator (lawss 1) (D1 p.2)); split => //.
exact: (dgpr_first_differential_operator (hD1 p.2 I)).
Qed.

(** Source for [dgpr_lemma31_q_first]: the values of D q_t(x), a chosen
    field (Federer 3.1.1); proof of lem:DGPR31. *)
Definition dgpr_lemma31_q_first (p : TX) : X -> R := projT1 (cid (dgpr_lemma31_q_values_exist p)).

(** Source for [dgpr_lemma31_q_firstP]: the chosen field gives the
    values of D q_t(x) for t < T. *)
Lemma dgpr_lemma31_q_firstP (t : R) (x : X) : t < T ->
  @dgpr_differential_values R n R^o A1 (fun z => Q (t, z)) x (dgpr_lemma31_q_first (t, x)).
Proof. by move=> ht; exact: (projT2 (cid (dgpr_lemma31_q_values_exist (t, x))) ht). Qed.

(** Source for [dgpr_lemma31_grad_log_q]: grad log q_t(x) =
    q(t,x)^(-1) grad q_t(x); proof of lem:DGPR31. *)
Definition dgpr_lemma31_grad_log_q (p : TX) : X :=
  (Q p)^-1 *: dgpr_gradient_values (dgpr_lemma31_q_first p).

(** Source for [dgpr_lemma31_hJ]: h_J = kappa rho + rho |grad log q|^2,
    which equals H(rho log q) by [dgpr_lemma31_heat_entropy]. *)
Definition dgpr_lemma31_hJ (p : TX) : R :=
  kappa p * rho p + rho p * N (dgpr_lemma31_grad_log_q p) ^+ 2.

(** Source for [dgpr_lemma31_min]: the function
    min{(T - t)^(-1) rho, (T - t)^(-1/2) R}, which dominates rho ||eta||^2
    (eq:31:eta, pointwise form). *)
Definition dgpr_lemma31_min (p : TX) : R :=
  Order.min ((T - p.1)^-1 * rho p) ((Num.sqrt (T - p.1))^-1 * Rr p).

(** Source for [dgpr_lemma31_m]: m(t) = min{gamma (T-t)^(-1),
    delta (T-t)^(-1/2)} of eq:31:eta. *)
Definition dgpr_lemma31_m (t : R) : R :=
  Order.min (gamma / (T - t)) (delta / Num.sqrt (T - t)).

Local Notation lQ := dgpr_lemma31_q_first.
Local Notation glq := dgpr_lemma31_grad_log_q.
Local Notation hJ := dgpr_lemma31_hJ.
Local Notation emin := dgpr_lemma31_min.

(** Source for [dgpr_lemma31_heat_J]: H(rho log q) = h_J on Omega_T,
    [dgpr_lemma31_heat_entropy]. *)
Lemma dgpr_lemma31_heat_J (t : R) (x : X) : t < T ->
  @dgpr_heat_operator R n R^o A1 (fun p : TX => rho p * LOG (Q p)) t x (hJ (t, x)).
Proof. by move=> ht; exact: (dgpr_lemma31_heat_entropy ht (dgpr_lemma31_q_firstP x ht)). Qed.

(** Source for [dgpr_lemma31_inner_bound]: for |B| <= Lambda and the
    values l of a linear map,
    -4 B . l(sum_i c_i eps_i) <= sum_i |l(eps_i)|^2 + 4 Lambda^2 sum_i c_i^2,
    by the Cauchy-Schwarz inequality and 4 Lambda a b <= a^2 + 4 Lambda^2 b^2
    (blueprint proof of lem:DGPR31). *)
Lemma dgpr_lemma31_inner_bound (Bv : Hom X Y) (lB : X -> Hom X Y) (c : 'I_n -> R) :
  NH Bv <= Lam -> (exists L : Hom X (Hom X Y), forall v, L v = lB v) ->
  - (4 * HI Bv (lB (\sum_i c i *: eps i))) <=
    \sum_(i < n) NH (lB (eps i)) ^+ 2 + 4 * Lam ^+ 2 * \sum_(i < n) c i ^+ 2.
Proof.
move=> hB [L hL].
have hL0 : 0 <= Lam := le_trans (inner_norm_nonnegative BH Bv) hB.
have e : lB (\sum_i c i *: eps i) = \sum_i c i *: lB (eps i).
  transitivity (L (\sum_i c i *: eps i)); first by rewrite hL.
  rewrite linear_sum; apply: eq_bigr => i _; rewrite -hL; exact: linearZ.
rewrite e (dgpr_inner_sumr BH) mulr_sumr -sumrN mulr_sumr -big_split /=.
apply: ler_sum => i _.
set a := NH (lB (eps i)); set h := HI Bv (lB (eps i)).
have ha : 0 <= a := inner_norm_nonnegative BH _.
have hh : `|h| <= Lam * a.
  apply: le_trans (inner_cauchy BH _ _) _.
  by apply: ler_wpM2r => //; exact: hB.
have hch : - (c i * h) <= `|c i| * `|h|.
  by rewrite -normrM -normrN; exact: ler_norm.
have hc0 := normr_ge0 (c i).
have hsq : c i ^+ 2 = `|c i| ^+ 2 by rewrite real_normK ?num_real.
have h2 := sqr_ge0 (a - 2 * Lam * `|c i|).
have h3 : `|c i| * `|h| <= `|c i| * (Lam * a) by exact: ler_wpM2l.
rewrite hsq; nra.
Qed.

(** Source for [dgpr_lemma31_coordinate_norm]: |sum_i c_i eps_i|^2 =
    sum_i c_i^2 for the standard orthonormal basis (Federer 1.7.5). *)
Lemma dgpr_lemma31_coordinate_norm (c : 'I_n -> R) :
  N (\sum_i c i *: eps i) ^+ 2 = \sum_(i < n) c i ^+ 2.
Proof.
rewrite (inner_norm_sqr BX).
rewrite (dgpr_orthonormal_parseval BX heX (@euclidean_coordinate_orthonormal_family R n)).
by apply: eq_bigr => i _; rewrite (dgpr_orthonormal_coefficient BX (@euclidean_coordinate_orthonormal_family R n)).
Qed.

(** Source for [dgpr_lemma31_grad_log_q_coordinates]: grad log q_t(x) =
    sum_i (q^(-1) D q_t(x)(eps_i)) eps_i. *)
Lemma dgpr_lemma31_grad_log_q_coordinates (p : TX) :
  glq p = \sum_i ((Q p)^-1 * lQ p (eps i)) *: eps i.
Proof.
rewrite /dgpr_lemma31_grad_log_q /dgpr_gradient_values scaler_sumr.
by apply: eq_bigr => i _; rewrite scalerA.
Qed.

Variable DB : TX -> X -> Hom X Y.
Hypothesis hDB : forall t x, t < T -> dgpr_differential_values NH (fun z => B (t, z)) x (DB (t, x)).

(** Source for [dgpr_lemma31_hK]: h_K = 2 rho |DB|^2 +
    4 rho B . DB(grad log q) + 2 kappa rho |B|^2, which equals
    H(rho |B|^2) by [dgpr_lemma31_heat_B2]. *)
Definition dgpr_lemma31_hK (p : TX) : R :=
  2 * rho p * \sum_(i < n) HI (DB p (eps i)) (DB p (eps i)) +
  4 * rho p * HI (B p) (DB p (glq p)) + 2 * kappa p * rho p * HI (B p) (B p).
Local Notation hK := dgpr_lemma31_hK.

(** Source for [dgpr_lemma31_integrand]: the integrand
    rho (|DB|^2 + |B(grad log rho)|^2) of lem:DGPR31, where |DB|^2 is the
    sum of |D B_t(x)(eps_i)|^2 for the field DB of space differentials. *)
Definition dgpr_lemma31_integrand (p : TX) : R :=
  rho p * (\sum_(i < n) NH (DB p (eps i)) ^+ 2 + NY (B p (dgpr_heat_grad_log_rho hS p)) ^+ 2).

(** Source for [dgpr_lemma31_heat_K]: H(rho |B|^2) = h_K on Omega_T,
    [dgpr_lemma31_heat_B2]. *)
Lemma dgpr_lemma31_heat_K (t : R) (x : X) : t < T ->
  @dgpr_heat_operator R n R^o A1 (fun p : TX => (rho p * HI (B p) (B p) : R^o)) t x (hK (t, x)).
Proof. by move=> ht; exact: (dgpr_lemma31_heat_B2 ht (hDB x ht) (dgpr_lemma31_q_firstP x ht)). Qed.

(** Source for [dgpr_lemma31_DB_bound]: blueprint proof of lem:DGPR31:
    rho |DB|^2 <= h_K + 4 Lambda^2 rho |grad log q|^2 on Omega_T, from
    |grad |B_t|^2| <= 2 Lambda |DB_t| and 4 Lambda a b <= a^2 + 4 Lambda^2 b^2;
    here |DB|^2 is the sum of |D B_t(x)(eps_i)|^2. *)
Lemma dgpr_lemma31_DB_bound (t : R) (x : X) : t < T ->
  rho (t, x) * \sum_(i < n) NH (DB (t, x) (eps i)) ^+ 2 <=
    hK (t, x) + 4 * Lam ^+ 2 * (rho (t, x) * N (glq (t, x)) ^+ 2).
Proof.
move=> ht.
have [[hr0 _] _ hk0 [_ hBL] _] := dgpr_identities_bounds_full hS x ht.
have [L [_ hL]] := hDB x ht.
have hI := dgpr_lemma31_inner_bound (fun i => (Q (t, x))^-1 * lQ (t, x) (eps i)) hBL
  (ex_intro _ L hL).
rewrite -(dgpr_lemma31_coordinate_norm (fun i => (Q (t, x))^-1 * lQ (t, x) (eps i))) in hI.
rewrite -(dgpr_lemma31_grad_log_q_coordinates (t, x)) in hI.
have eS : \sum_(i < n) HI (DB (t, x) (eps i)) (DB (t, x) (eps i)) =
    \sum_(i < n) NH (DB (t, x) (eps i)) ^+ 2.
  by apply: eq_bigr => i _; rewrite /hom_norm (inner_norm_sqr BH).
have hBB : 0 <= HI (B (t, x)) (B (t, x)) by rewrite -(inner_norm_sqr BH); exact: sqr_ge0.
rewrite /dgpr_lemma31_hK eS.
move: hI hBB; set s := \sum_(i < n) NH (DB (t, x) (eps i)) ^+ 2.
set g := N _ ^+ 2; set h := HI (B (t, x)) _; set b := HI (B (t, x)) (B (t, x)).
move=> hI hBB.
have hkb : 0 <= kappa (t, x) * rho (t, x) * b by rewrite mulr_ge0 // mulr_ge0 // ltW.
have hrI := ler_wpM2l (ltW hr0) hI.
nra.
Qed.

(** Source for [dgpr_lemma31_rho_first]: D rho_t(x) has the values
    [dgpr_heat_rho_first] (lem:heat_extension(1)). *)
Lemma dgpr_lemma31_rho_first (t : R) (x : X) : t < T ->
  @dgpr_differential_values R n R^o A1 (fun z => rho (t, z)) x (dgpr_heat_rho_first hS t x).
Proof.
move=> ht.
have [_ [h1 _]] := dgpr_backward_heat_jet hmu0 hZ1 hOmu0 hMmu0 hsep1 (dgpr_one_measurable hmu0)
  (@dgpr_one_bound1 R n) x ht.
exact: h1.
Qed.

(** Source for [dgpr_lemma31_integrand_bound]: blueprint proof of
    lem:DGPR31, combination of (eq:31:eta), the bound of |B(grad log rho)|^2
    and the bound of rho |DB|^2: on Omega_T,
    rho (|DB|^2 + |B(grad log rho)|^2) <=
    (1 + 4n) h_K + (16 n + 6) Lambda^2 h_J + 4 min{(T-t)^(-1) rho, (T-t)^(-1/2) R}. *)
Lemma dgpr_lemma31_integrand_bound (t : R) (x : X) : t < T ->
  rho (t, x) * (\sum_(i < n) NH (DB (t, x) (eps i)) ^+ 2 +
    NY (B (t, x) (dgpr_heat_grad_log_rho hS (t, x))) ^+ 2) <=
  (1 + 4 * n%:R) * hK (t, x) + (16 * n%:R + 6) * Lam ^+ 2 * hJ (t, x) + 4 * emin (t, x).
Proof.
move=> ht.
have [[hr0 _] _ hk0 _ _] := dgpr_identities_bounds_full hS x ht.
have hBg := dgpr_lemma31_B_gradient_bound ht (hDB x ht) (dgpr_lemma31_q_firstP x ht)
  (dgpr_lemma31_rho_first x ht).
have [he1 he2] := dgpr_lemma31_eta_pointwise hS x ht.
have hDBb := dgpr_lemma31_DB_bound x ht.
have hn0 : 0 <= n%:R :> R := ler0n _ _.
have hL2 : 0 <= Lam ^+ 2 := sqr_ge0 _.
have hemin : rho (t, x) * ND (eta (t, x)) ^+ 2 <= emin (t, x).
  rewrite /dgpr_lemma31_min /= le_min; apply/andP; split.
  - by rewrite [X in _ <= X]mulrC; exact: he1.
  - by rewrite [X in _ <= X]mulrC; exact: he2.
have hJg : rho (t, x) * N (glq (t, x)) ^+ 2 <= hJ (t, x).
  by rewrite /dgpr_lemma31_hJ lerDr mulr_ge0 // ltW.
have hg0 : 0 <= rho (t, x) * N (glq (t, x)) ^+ 2 by rewrite mulr_ge0 ?sqr_ge0 // ltW.
have hs0 : 0 <= \sum_(i < n) NH (DB (t, x) (eps i)) ^+ 2 by apply: sumr_ge0 => i _; exact: sqr_ge0.
have hBg' := ler_wpM2l (ltW hr0) hBg.
move: hBg' hemin hJg hg0 hs0 hDBb.
set s := \sum_(i < n) NH (DB (t, x) (eps i)) ^+ 2; set b := NY _ ^+ 2.
set e := ND _ ^+ 2; set g := N _ ^+ 2; set r := rho (t, x).
move=> hBg' hemin hJg hg0 hs0 hDBb.
have h1 : (1 + 4 * n%:R) * (r * s) <= (1 + 4 * n%:R) * (hK (t, x) + 4 * Lam ^+ 2 * (r * g)).
  by apply: ler_wpM2l => //; rewrite addr_ge0 // mulr_ge0.
have h2 : (16 * n%:R + 6) * Lam ^+ 2 * (r * g) <= (16 * n%:R + 6) * Lam ^+ 2 * hJ (t, x).
  by apply: ler_wpM2l => //; rewrite mulr_ge0 // addr_ge0 // mulr_ge0.
nra.
Qed.

(** Source for [dgpr_lemma31_min_integral]: blueprint proof of
    lem:DGPR31, (eq:31:eta) integrated: for t < T the function
    min{(T-t)^(-1) rho_t, (T-t)^(-1/2) R_t} is L^n summable, with integral
    at most m(t), by lem:identities(mass) and Federer 2.4.4(5). *)
Lemma dgpr_lemma31_min_integral (t : R) : t < T -> exists e : R,
  is_measure_integral LL (real_total_integrand (fun x => emin (t, x))) e%:E /\ e <= dgpr_lemma31_m t.
Proof.
move=> ht.
have [_ hR _ hr] := dgpr_identities_mass hS ht.
have h1 := real_total_integral_scale hLL (T - t)^-1 hr.
have h2 := real_total_integral_scale hLL (Num.sqrt (T - t))^-1 hR.
have hs1 : summable_real_functions LL (fun x => (T - t)^-1 * rho (t, x)).
  by exists ((T - t)^-1 * gamma).
have hs2 : summable_real_functions LL (fun x => (Num.sqrt (T - t))^-1 * Rr (t, x)).
  by exists ((Num.sqrt (T - t))^-1 * delta).
have hs := summable_real_minimum hLL hs1 hs2.
have [e he] := hs.
exists e; split; first exact: he.
rewrite /dgpr_lemma31_m le_min; apply/andP; split.
- rewrite mulrC; apply: (dgpr_integral_le hLL _ he h1) => x; by rewrite ge_min lexx.
- rewrite mulrC; apply: (dgpr_integral_le hLL _ he h2) => x; by rewrite ge_min lexx orbT.
Qed.

(** Source for [dgpr_lemma31_time_slice]: blueprint proof of lem:DGPR31
    at a fixed time t < T: if ∫ h_J(t,.) = a and ∫ h_K(t,.) = b, then
    the upper integral of rho_t (|DB_t|^2 + |B_t(grad log rho_t)|^2) is at
    most (1 + 4n) b + (16 n + 6) Lambda^2 a + 4 m(t), and this number is
    nonnegative. *)
Lemma dgpr_lemma31_time_slice (t a b : R) : t < T ->
  is_measure_integral LL (real_total_integrand (fun x => hJ (t, x))) a%:E ->
  is_measure_integral LL (real_total_integrand (fun x => hK (t, x))) b%:E ->
  0 <= (1 + 4 * n%:R) * b + (16 * n%:R + 6) * Lam ^+ 2 * a + 4 * dgpr_lemma31_m t /\
  (measure_upper_integral LL (real_total_integrand (fun x => dgpr_lemma31_integrand (t, x)))
   <= ((1 + 4 * n%:R) * b + (16 * n%:R + 6) * Lam ^+ 2 * a + 4 * dgpr_lemma31_m t)%:E)%E.
Proof.
move=> ht ha hb.
have [e [he hem]] := dgpr_lemma31_min_integral ht.
have hG1 := real_total_integral_scale hLL (1 + 4 * n%:R) hb.
have hG2 := real_total_integral_scale hLL ((16 * n%:R + 6) * Lam ^+ 2) ha.
have hG3 := real_total_integral_scale hLL 4 he.
have hG := real_total_integral_add hLL (real_total_integral_add hLL hG1 hG2) hG3.
have hle x : dgpr_lemma31_integrand (t, x) <=
    (1 + 4 * n%:R) * hK (t, x) + (16 * n%:R + 6) * Lam ^+ 2 * hJ (t, x) + 4 * emin (t, x).
  exact: dgpr_lemma31_integrand_bound x ht.
have hge x : 0 <= dgpr_lemma31_integrand (t, x).
  have [[hr0 _] _ _ _ _] := dgpr_identities_bounds_full hS x ht.
  apply: mulr_ge0; first exact: ltW.
  by apply: addr_ge0; [apply: sumr_ge0 => i _; exact: sqr_ge0 | exact: sqr_ge0].
have hG0 : 0 <= (1 + 4 * n%:R) * b + (16 * n%:R + 6) * Lam ^+ 2 * a + 4 * e.
  apply: (dgpr_integral_ge0 hLL _ hG) => x; exact: le_trans (hge x) (hle x).
have hm4 : 4 * e <= 4 * dgpr_lemma31_m t by rewrite ler_pM2l.
split; first by apply: le_trans hG0 _; rewrite lerD2l.
apply: le_trans (dgpr_upper_integral_le hLL hle hG) _.
by rewrite lee_fin lerD2l.
Qed.

(** Source for [dgpr_lemma31_K_bound]: blueprint proof of lem:DGPR31:
    0 <= ∫ rho_t |B_t|^2 dL^n <= Lambda^2 gamma, by |B| <= Lambda
    (lem:identities(bounds)) and ∫ rho_t dL^n = gamma (mass). *)
Lemma dgpr_lemma31_K_bound (t k : R) : t < T ->
  is_measure_integral LL (real_total_integrand (fun x => rho (t, x) * HI (B (t, x)) (B (t, x)))) k%:E ->
  0 <= k <= Lam ^+ 2 * gamma.
Proof.
move=> ht hk.
have [_ _ _ hr] := dgpr_identities_mass hS ht.
have hr2 := real_total_integral_scale hLL (Lam ^+ 2) hr.
have hB x : 0 <= HI (B (t, x)) (B (t, x)) <= Lam ^+ 2.
  have [[hr0 _] _ _ [_ hBL] _] := dgpr_identities_bounds_full hS x ht.
  rewrite -(inner_norm_sqr BH) sqr_ge0 /=.
  by rewrite lerXn2r ?nnegrE ?inner_norm_nonnegative // (le_trans (inner_norm_nonnegative BH _) hBL).
apply/andP; split.
- apply: (dgpr_integral_ge0 hLL _ hk) => x.
  have [[hr0 _] _ _ _ _] := dgpr_identities_bounds_full hS x ht.
  by have /andP [h0 _] := hB x; rewrite mulr_ge0 // ltW.
- apply: (dgpr_integral_le hLL _ hk hr2) => x.
  have [[hr0 _] _ _ _ _] := dgpr_identities_bounds_full hS x ht.
  have /andP [_ h1] := hB x.
  by rewrite mulrC; apply: ler_wpM2r => //; exact: ltW.
Qed.

End Lemma31Integrals.
