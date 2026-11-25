(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3, (3.16):
    log-semiconvexity of heat extensions; blueprint dgpr_blueprint.tex,
    lem:heat_extension(3), second inequality, and lem:semiconvex. Here Z = R,
    f = 1 or f >= 0, nu is a finite measure with nu(R^n) = m > 0, every
    open set is nu measurable, and nu(R^n without B(0,r)) = 0. The gradient
    bound |grad log u_s(x)| <= (2s)^(-1)(|x| + r) is stated through the
    differential: |D log u_s(x)(w)| <= (2s)^(-1)(|x| + r)|w| for every w. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm InnerNormInequalities PartialFunctionUP PartialFunctionBasic MeasureUP
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureVectorIntegralUP SummableRealFunctionUP
  SummableRealArithmetic LatticeL1ApproximationLaws CompleteMetricUP VectorDaniellHypotheses NormClassOneUP
  MeasurableFunctionUP MeasurableTotalBasic MeasureAlmostUP ScalarNormMetricCompleteness LocalUniquenessExample
  ScalarVectorIntegralIdentification NormDifferentialUP NormDifferentialChain NormDifferentialBilinearProduct
  NormBilinearDifferentialAlgebra NormHigherCurveDerivativeUP ScalarReciprocalDifferential
  RealLogarithmDifferential RealExponentialUP RealExponentialSealed CircularTrigonometrySealed.
From DPGPR Require Import DgprParameterIntegralDifferential DgprHeatKernel DgprHeatKernelDifferential
  DgprHeatExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Semiconvex.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation B := (@euclidean_inner_product R n).
Local Notation p := (@dgpr_heat_kernel R n).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation hZ1 := (@scalar_norm_metric_complete R).
Local Notation hsep1 := (scalar_norm_separable R).
Variable nu : set X -> \bar R.
Hypothesis hnu : is_measure nu.
Hypothesis hOpen : forall A : set X, @open (real_norm_metric_space hN) A -> measure_measurable nu A.
Variable m : R.
Hypothesis hmass : nu setT = m%:E.
Variable r : R.
Hypothesis hsupp : measure_almost_everywhere nu [set y | N y <= r].

(** Source for [dgpr_real_convolution_integral]: for Z = R the vector
    integral of 2.4.12 is the real integral (Federer 2.4.12); blueprint
    lem:semiconvex, proof. *)
Lemma dgpr_real_convolution_integral (g : X -> R^o) (M : R) (k : X -> R) (K : R) (x : X) :
  is_measure_measurable_function nu (partial_function_total (fun y => (g y : real_norm_metric_space hA))) ->
  (forall y, `|g y| <= M) ->
  norm_class_zero N A1 setT k -> (forall z, `|k z| <= K) ->
  is_measure_integral nu (real_total_integrand (fun y => k (x - y) * g y))
    (dgpr_convolution hnu hZ1 g k x)%:E.
Proof.
move=> hg hM hk hK.
have h := dgpr_convolution_integral hnu hZ1 hOpen hmass hsep1 hg hM x hk hK.
exact: (scalar_vector_integral_identification h).
Qed.

(** Source for [dgpr_one_measurable]: the constant function 1 is nu
    measurable; blueprint lem:semiconvex (the heat extension of (nu,1)). *)
Lemma dgpr_one_measurable :
  is_measure_measurable_function nu (partial_function_total (fun _ : X => (1 : real_norm_metric_space hA))).
Proof.
exact: (@measurable_total_constant R X [the topologicalType of real_norm_metric_space hA] nu hnu
  (1 : real_norm_metric_space hA)).
Qed.

(** Source for [dgpr_one_bound]: the constant function 1 is bounded;
    blueprint lem:semiconvex. *)
Lemma dgpr_one_bound (y : X) : `|(fun _ : X => 1 : R^o) y| <= 1.
Proof. by rewrite normr1. Qed.

(** Source for [dgpr_one_integral]: the convolution of a bounded
    continuous kernel with nu is the real integral of [y |-> k(x-y)];
    blueprint lem:semiconvex, proof. *)
Lemma dgpr_one_integral (k : X -> R) (K : R) (x : X) :
  norm_class_zero N A1 setT k -> (forall z, `|k z| <= K) ->
  is_measure_integral nu (real_total_integrand (fun y => k (x - y)))
    (dgpr_convolution hnu hZ1 (fun _ => 1 : R^o) k x)%:E.
Proof.
move=> hk hK.
have h := @dgpr_real_convolution_integral (fun _ => 1 : R^o) 1 k K x dgpr_one_measurable
  dgpr_one_bound hk hK.
apply: (measure_integral_graph_equivalent _ h) => y z.
by rewrite !real_total_integrand_graph mulr1.
Qed.

(** Source for [dgpr_heat_extension_lower]: DPGPR 2026, section 3;
    blueprint lem:heat_extension(3), second inequality: for Z = R and
    f >= 0, u(s,x) >= (4 pi s)^(-n/2) exp(-(|x| + r)^2/(4s)) times the
    integral of f d nu. *)
Theorem dgpr_heat_extension_lower (g : X -> R^o) (M b s : R) (x : X) : 0 < s ->
  is_measure_measurable_function nu (partial_function_total (fun y => (g y : real_norm_metric_space hA))) ->
  (forall y, `|g y| <= M) -> (forall y, 0 <= g y) ->
  is_measure_integral nu (real_total_integrand g) b%:E ->
  dgpr_kernel_constant n s * RealExponential.exponential (- (N x + r) ^+ 2 / (4 * s)) * b <=
    dgpr_heat_extension hnu hZ1 g s x.
Proof.
move=> hs hg hM hg0 hb.
have h := @dgpr_real_convolution_integral g M (p s) (dgpr_kernel_constant n s) x hg hM
  (dgpr_kernel_class_zero hs) (fun z => dgpr_kernel_abs_le z hs).
have hb' := real_total_integral_scale hnu
  (dgpr_kernel_constant n s * RealExponential.exponential (- (N x + r) ^+ 2 / (4 * s))) hb.
apply: (dgpr_integral_le_on_ball hnu hsupp hb' h) => y hy.
apply: ler_wpM2r; first exact: hg0.
rewrite /dgpr_heat_kernel -/(dgpr_kernel_constant n s); apply: ler_wpM2l.
  exact: dgpr_kernel_constant_ge0.
apply: dgpr_exponential_le; rewrite !mulNr lerN2; apply: ler_wpM2r.
  by rewrite invr_ge0 ltW // mulr_gt0.
have hd := dgpr_distance_upper x hy.
have hN0 := inner_norm_nonnegative (@euclidean_inner_productP R n) (x - y).
have hx0 : 0 <= N x + r by apply: le_trans hd.
by rewrite ler_sqr.
Qed.

Local Notation U s := (dgpr_heat_extension hnu hZ1 (fun _ : X => 1 : R^o) s).
Local Notation DU s w := (dgpr_convolution hnu hZ1 (fun _ : X => 1 : R^o)
  (fun z => @dgpr_kernel_differential R n s z w)).
Local Notation D2U s v w := (dgpr_convolution hnu hZ1 (fun _ : X => 1 : R^o)
  (fun z => @dgpr_kernel_second R n s z v w)).

Hypothesis hm0 : 0 < m.

(** Source for [dgpr_heat_extension_positive]: u_s(x) > 0 for the heat
    extension of (nu,1) when nu(R^n) > 0; blueprint lem:semiconvex, proof. *)
Theorem dgpr_heat_extension_positive (s : R) (x : X) : 0 < s -> 0 < U s x.
Proof.
move=> hs.
have hb : is_measure_integral nu (real_total_integrand (fun _ : X => (1 : R^o))) m%:E.
  by have := dgpr_constant_integral hnu hmass 1; rewrite mul1r.
have h := @dgpr_heat_extension_lower (fun _ => 1 : R^o) 1 m s x hs dgpr_one_measurable
  dgpr_one_bound (fun _ => ler01) hb.
apply: lt_le_trans h; rewrite mulr_gt0 // mulr_gt0 //.
  by rewrite /dgpr_kernel_constant invr_gt0 exprn_gt0 // sqrtr_gt0 mulr_gt0 // mulr_gt0 // dgpr_pi_gt0.
exact: (real_exponential_positive (@RealExponential.laws R) _).
Qed.

(** Source for [dgpr_unit_kernel_integral]: u_s(x) is the integral of
    [y |-> p_s(x-y)] with respect to nu; blueprint lem:semiconvex, proof. *)
Lemma dgpr_unit_kernel_integral (s : R) (x : X) : 0 < s ->
  is_measure_integral nu (real_total_integrand (fun y => p s (x - y))) (U s x)%:E.
Proof.
move=> hs; exact: (dgpr_one_integral x (dgpr_kernel_class_zero hs) (fun z => dgpr_kernel_abs_le z hs)).
Qed.

(** Source for [dgpr_unit_first_integral]: D u_s(x)(w) is the integral of
    [y |-> D p_s(x-y)(w)]; blueprint lem:semiconvex, proof. *)
Lemma dgpr_unit_first_integral (s : R) (x w : X) : 0 < s ->
  is_measure_integral nu (real_total_integrand (fun y => @dgpr_kernel_differential R n s (x - y) w))
    (DU s w x)%:E.
Proof.
move=> hs; exact: (dgpr_one_integral x (dgpr_kernel_first_class_zero w hs)
  (fun z => dgpr_kernel_differential_bound z w hs)).
Qed.

(** Source for [dgpr_unit_second_integral]: D^2 u_s(x)(v,w) is the integral
    of [y |-> D^2 p_s(x-y)(v,w)]; blueprint lem:semiconvex, proof. *)
Lemma dgpr_unit_second_integral (s : R) (x v w : X) : 0 < s ->
  is_measure_integral nu (real_total_integrand (fun y => @dgpr_kernel_second R n s (x - y) v w))
    (D2U s v w x)%:E.
Proof.
move=> hs; exact: (dgpr_one_integral x (dgpr_kernel_second_class_zero v w hs)
  (fun z => dgpr_kernel_second_bound z v w hs)).
Qed.

(** Source for [dgpr_semiconvex]: DPGPR 2026, (3.16); blueprint
    lem:semiconvex. With u the heat extension of (nu,1): log u_s has at x the
    differential [w |-> D u_s(x)(w)/u_s(x)], whose values are at most
    (2s)^(-1)(|x| + r)|w| in absolute value, and the differential at x of
    [y |-> D u_s(y)(v)/u_s(y)], that is D^2 log u_s(x)(v,.), takes at v a
    value at least -(2s)^(-1)|v|^2. The variance inequality replaces the
    appeal to Hoelder's inequality 2.4.14. *)
Theorem dgpr_semiconvex (s : R) (x v : X) : 0 < s ->
  (exists G : Hom X R^o,
    has_norm_differential N A1 setT (fun y => RealExponential.logarithm (U s y)) x G /\
    forall w, G w = DU s w x / U s x) /\
  (forall w, `|DU s w x / U s x| <= (2 * s)^-1 * (N x + r) * N w) /\
  (exists H : Hom X R^o,
    has_norm_differential N A1 setT (fun y => DU s v y / U s y) x H /\
    - ((2 * s)^-1 * N v ^+ 2) <= H v).
Proof.
move=> hs.
have hpos y := dgpr_heat_extension_positive y hs.
have hs2 : 0 < 2 * s by rewrite mulr_gt0.
have hs2i : 0 < (2 * s)^-1 by rewrite invr_gt0.
have [L1 [hL1 hL1v]] := dgpr_heat_extension_first hnu hZ1 hOpen hmass hsep1 dgpr_one_measurable
  dgpr_one_bound x hs.
have I0 := dgpr_unit_kernel_integral x hs.
split.
  have hlog := real_logarithm_differential (hpos x).
  have hG := norm_differential_chain hN hA hA hL1 hlog.
  rewrite dgpr_setT_and in hG.
  exists (hom_comp (real_logarithm_linear_term (U s x)) L1); split; first exact: hG.
  move=> w; rewrite hom_compE hL1v.
  by change ((U s x)^-1 * DU s w x = DU s w x / U s x); rewrite mulrC.
split.
  move=> w; set K := (2 * s)^-1 * (N x + r) * N w.
  have I1 := dgpr_unit_first_integral x w hs.
  have hpt y : N y <= r -> `|@dgpr_kernel_differential R n s (x - y) w| <= K * p s (x - y).
    move=> hy; have hp := dgpr_kernel_gt0 (x - y) hs.
    rewrite dgpr_kernel_differentialE normrM (gtr0_norm hp) normrM normrN.
    rewrite (gtr0_norm hs2i); apply: ler_wpM2r; first exact: ltW.
    rewrite /K -mulrA; apply: ler_wpM2l; first exact: ltW.
    apply: le_trans (inner_cauchy (@euclidean_inner_productP R n) (x - y) w) _.
    apply: ler_wpM2r; first exact: (inner_norm_nonnegative (@euclidean_inner_productP R n)).
    exact: dgpr_distance_upper.
  have hup := dgpr_integral_le_on_ball hnu hsupp I1 (real_total_integral_scale hnu K I0)
    (fun y hy => le_trans (ler_norm _) (hpt y hy)).
  have hpt' y : N y <= r -> - K * p s (x - y) <= @dgpr_kernel_differential R n s (x - y) w.
    by move=> hy; have := hpt y hy; rewrite ler_norml mulNr => /andP [].
  have hlo := dgpr_integral_le_on_ball hnu hsupp (real_total_integral_scale hnu (- K) I0) I1 hpt'.
  rewrite normrM normfV (gtr0_norm (hpos x)) ler_pdivrMr //.
  by rewrite ler_norml hup andbT -mulNr.
have [L2 [hL2 hL2v]] := dgpr_heat_extension_second hnu hZ1 hOpen hmass hsep1 dgpr_one_measurable
  dgpr_one_bound v x hs.
have hinv := scalar_reciprocal_differential (lt0r_neq0 (hpos x)).
have hU' := norm_differential_chain hN hA hA hL1 hinv.
have eA : (fun y : X => setT y /\ U s y != 0) = setT.
  by apply: funext => y; apply: propext; split => // _; split => //; exact: lt0r_neq0 (hpos y).
rewrite eA in hU'.
have hM a b : A1 (a * b : R^o) <= 1 * (A1 a * A1 b) by rewrite mul1r normrM.
have hQ := norm_differential_bilinear_product hN hA hA hA (dgpr_mul_bilinear R) (@ler01 R) hM hL2 hU'.
eexists; split; first exact: hQ.
change (- ((2 * s)^-1 * N v ^+ 2) <=
  L2 v * (U s x)^-1 + DU s v x * (L1 v * - ((U s x)^-1) ^+ 2)).
rewrite hL2v hL1v.
have I1 := dgpr_unit_first_integral x v hs.
have I2 := dgpr_unit_second_integral x v v hs.
set J1 := DU s v x; set J2 := D2U s v v x; set u := U s x.
set a := - (2 * s) * J1 / u.
have hA2 := real_total_integral_scale hnu (4 * s ^+ 2) I2.
have hB0 := real_total_integral_scale hnu (2 * s * N v ^+ 2) I0.
have hC1 := real_total_integral_scale hnu (4 * s * a) I1.
have hD0 := real_total_integral_scale hnu (a ^+ 2) I0.
have hsum := real_total_integral_add hnu hA2 (real_total_integral_add hnu hB0
  (real_total_integral_add hnu hC1 hD0)).
have hI0 := dgpr_integral_le_on_ball hnu hsupp (real_total_zero_integral hnu) hsum.
have hu : 0 < u := hpos x.
have hI : 0 <= 4 * s ^+ 2 * J2 + (2 * s * N v ^+ 2 * u + (4 * s * a * J1 + a ^+ 2 * u)).
  apply: hI0 => y _.
  have hp := dgpr_kernel_gt0 (x - y) hs.
  rewrite dgpr_kernel_secondE dgpr_kernel_differentialE
    (inner_norm_sqr (@euclidean_inner_productP R n) v).
  have -> : 4 * s ^+ 2 * (((4 * s ^+ 2)^-1 * B (x - y) v * B (x - y) v - (2 * s)^-1 * B v v) *
      p s (x - y)) + (2 * s * B v v * p s (x - y) + (4 * s * a * (- (2 * s)^-1 *
      B (x - y) v * p s (x - y)) + a ^+ 2 * p s (x - y))) =
    (B (x - y) v - a) ^+ 2 * p s (x - y).
    by field; rewrite lt0r_neq0.
  by rewrite mulr_ge0 ?sqr_ge0 // ltW.
have e : J2 / u + J1 * (J1 * - u^-1 ^+ 2) + (2 * s)^-1 * N v ^+ 2 =
    (4 * s ^+ 2 * J2 + (2 * s * N v ^+ 2 * u + (4 * s * a * J1 + a ^+ 2 * u))) / (4 * s ^+ 2 * u).
  by rewrite /a; field; rewrite !lt0r_neq0.
rewrite -subr_ge0 opprK e; apply: divr_ge0; first exact: hI.
apply: mulr_ge0; last exact: ltW.
by apply: mulr_ge0; [by [] | exact: sqr_ge0].
Qed.

End Semiconvex.
