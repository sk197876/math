(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3, bounds of
    the heat kernel and of heat extensions in the form of the blueprint
    dgpr_blueprint.tex: lem:kernel(4) for j = 1, 2 with c(n,1) = 1/2 and
    c(n,2) = 1, lem:heat_extension(2) for j = 0, 1, 2, and the first
    inequality of lem:heat_extension(3) without assuming the existence of
    the integrals. Here s^(-1/2) is written (sqrt s)^(-1), and the operator
    norm bound ||L|| <= K of a j linear map L is stated as
    |L(v_1, ..., v_j)| <= K |v_1| ... |v_j| for all v_1, ..., v_j. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric NormMetricContinuity NormMetricScaleContinuity
  HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm InnerNormInequalities PartialFunctionUP PartialFunctionBasic MeasureUP
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureVectorIntegralUP SummableRealFunctionUP
  SummableRealArithmetic CompleteMetricUP VectorDaniellHypotheses NormClassOneUP NormClassZeroArithmetic
  MeasurableFunctionUP MeasurableTotalBasic BorelFunctionBasic MeasureAlmostUP MeasureAlmostBasic
  ScalarNormMetricCompleteness LocalUniquenessExample TotalVectorIntegralAlmostDominatedNorm
  NormDifferentialUP RealExponentialUP RealExponentialSealed CircularTrigonometrySealed.
From DPGPR Require Import DgprParameterIntegralDifferential DgprHeatKernel DgprHeatKernelDifferential
  DgprHeatExtension DgprHeatSemiconvex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section KernelScaledBounds.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation B := (@euclidean_inner_product R n).
Local Notation p := (@dgpr_heat_kernel R n).

(** Source for [dgpr_kernel_first_scaled_bound]: DPGPR 2026, section 3;
    blueprint lem:kernel(4), case j = 1, with c(n,1) = 1/2:
    |D p_s(z)(v)| <= 2^(-1) s^(-1/2) (1 + |z| s^(-1/2)) p_s(z) |v|. *)
Theorem dgpr_kernel_first_scaled_bound (s : R) (z v : X) : 0 < s ->
  `|dgpr_kernel_differential s z v| <=
    2^-1 * (Num.sqrt s)^-1 * (1 + N z / Num.sqrt s) * p s z * N v.
Proof.
move=> hs; have hp := dgpr_kernel_gt0 z hs.
have hNn y : 0 <= N y := inner_norm_nonnegative (@euclidean_inner_productP R n) y.
have hC := inner_cauchy (@euclidean_inner_productP R n) z v.
have h2 : 0 < (2 * s)^-1 by rewrite invr_gt0 mulr_gt0.
rewrite dgpr_kernel_differentialE normrM (gtr0_norm hp) normrM normrN (gtr0_norm h2).
have hq : 0 < Num.sqrt s by rewrite sqrtr_gt0.
have hsq : s = Num.sqrt s ^+ 2 by rewrite sqr_sqrtr // ltW.
have e : (2 * s)^-1 = 2^-1 * (Num.sqrt s)^-1 * (Num.sqrt s)^-1.
  by rewrite {1}hsq expr2 !invfM mulrA.
rewrite e; move: (Num.sqrt s) hq => q hq; move: (p s z) hp => P hP.
set c := q^-1; have hc : 0 < c by rewrite invr_gt0.
have -> : 2^-1 * c * c * `|B z v| * P = (2^-1 * c * c * P) * `|B z v| by ring.
have -> : 2^-1 * c * (1 + N z * c) * P * N v = (2^-1 * c * c * P) * (N z * N v) + 2^-1 * c * P * N v.
  by ring.
have hc0 := ltW hc; have hP0 := ltW hP.
have hA : 0 <= 2^-1 * c * c * P by rewrite !mulr_ge0 // invr_ge0.
apply: le_trans (ler_wpM2l hA hC) _.
by rewrite lerDl !mulr_ge0 // invr_ge0.
Qed.

(** Source for [dgpr_kernel_second_scaled_bound]: DPGPR 2026, section 3;
    blueprint lem:kernel(4), case j = 2, with c(n,2) = 1:
    |D^2 p_s(z)(v,w)| <= s^(-1) (1 + |z| s^(-1/2))^2 p_s(z) |v| |w|. *)
Theorem dgpr_kernel_second_scaled_bound (s : R) (z v w : X) : 0 < s ->
  `|dgpr_kernel_second s z v w| <=
    s^-1 * (1 + N z / Num.sqrt s) ^+ 2 * p s z * N v * N w.
Proof.
move=> hs; have hp := dgpr_kernel_gt0 z hs.
have hNn x : 0 <= N x := inner_norm_nonnegative (@euclidean_inner_productP R n) x.
have hC x y : `|B x y| <= N x * N y := inner_cauchy (@euclidean_inner_productP R n) x y.
set a := (4 * s ^+ 2)^-1; set b := (2 * s)^-1.
have ha : 0 <= a by rewrite invr_ge0 mulr_ge0 // ltW // exprn_gt0.
have hb : 0 <= b by rewrite invr_ge0 mulr_ge0 // ltW.
rewrite dgpr_kernel_secondE -/a -/b normrM (gtr0_norm hp).
have hX : `|a * B z v * B z w| <= a * N z ^+ 2 * (N v * N w).
  have e1 : `|a * B z v * B z w| = a * (`|B z v| * `|B z w|).
    by rewrite normrM normrM (ger0_norm ha) mulrA.
  have e2 : a * N z ^+ 2 * (N v * N w) = a * ((N z * N v) * (N z * N w)) by ring.
  rewrite e1 e2; apply: ler_wpM2l => //.
  by apply: ler_pM; [exact: normr_ge0 | exact: normr_ge0 | exact: hC | exact: hC].
have hY : `|b * B v w| <= b * (N v * N w) by rewrite normrM (ger0_norm hb) ler_wpM2l.
have hXY := le_trans (ler_normB _ _) (lerD hX hY).
apply: le_trans (ler_wpM2r (ltW hp) hXY) _.
have hq : 0 < Num.sqrt s by rewrite sqrtr_gt0.
have hsq : s = Num.sqrt s ^+ 2 by rewrite sqr_sqrtr // ltW.
set c := (Num.sqrt s)^-1.
have hc : 0 < c by rewrite invr_gt0.
have es : s^-1 = c ^+ 2 by rewrite /c exprVn -hsq.
have ea : a = 4^-1 * c ^+ 2 * c ^+ 2 by rewrite /a -es expr2 !invfM mulrA.
have eb : b = 2^-1 * c ^+ 2 by rewrite /b invfM -es.
rewrite ea eb es; move: (p s z) hp => P hP.
have hle : 4^-1 * (N z * c) ^+ 2 + 2^-1 <= (1 + N z * c) ^+ 2.
  have hy : 0 <= N z * c by rewrite mulr_ge0 // ltW.
  move: (N z * c) hy => y hy; nra.
have -> : (4^-1 * c ^+ 2 * c ^+ 2 * N z ^+ 2 * (N v * N w) + 2^-1 * c ^+ 2 * (N v * N w)) * P =
  (c ^+ 2 * (P * (N v * N w))) * (4^-1 * (N z * c) ^+ 2 + 2^-1) by ring.
have -> : c ^+ 2 * (1 + N z * c) ^+ 2 * P * N v * N w =
  (c ^+ 2 * (P * (N v * N w))) * (1 + N z * c) ^+ 2 by ring.
have hc0 := ltW hc; have hP0 := ltW hP.
by apply: ler_wpM2l => //; rewrite !mulr_ge0 // exprn_ge0.
Qed.

End KernelScaledBounds.

Section HeatBounds.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation p := (@dgpr_heat_kernel R n).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation hZ1 := (@scalar_norm_metric_complete R).
Local Notation exp := (@RealExponential.exponential R).
Variable nu : set X -> \bar R.
Hypothesis hnu : is_measure nu.
Variable Z : lmodType R.
Variable NZ : Z -> R.
Hypothesis hNZ : is_real_norm NZ.
Hypothesis hZ : is_complete_metric_space (real_norm_metric_space hNZ).
Variable f : X -> Z.
Hypothesis hOpen : forall A : set X, @open (real_norm_metric_space hN) A -> measure_measurable nu A.
Variable m : R.
Hypothesis hmass : nu setT = m%:E.
Hypothesis hsep : is_separable_normed_space hNZ.
Hypothesis hfmeas : is_measure_measurable_function nu
  (partial_function_total (fun y => (f y : real_norm_metric_space hNZ))).
Variable M : R.
Hypothesis hfM : forall y, NZ (f y) <= M.
Local Notation conv := (@dgpr_convolution R n nu hnu Z NZ hNZ hZ f).
Local Notation u := (@dgpr_heat_extension R n nu hnu Z NZ hNZ hZ f).

(** Source for [dgpr_norm_measurable]: [y |-> |f(y)|] is nu measurable,
    since the norm is Lipschitz, hence continuous and Borel (Federer 2.3.2,
    2.3.5); blueprint lem:heat_extension(2),(3). *)
Lemma dgpr_norm_measurable :
  is_measure_measurable_function nu
    (partial_function_total (fun y => (NZ (f y) : real_norm_metric_space hA))).
Proof.
have hc : continuous (fun z : real_norm_metric_space hNZ => (NZ z : real_norm_metric_space hA)).
  apply: (@metric_fixed_lipschitz_continuous R _ _ _ 1 ler01) => a b.
  rewrite !real_norm_metric_distanceE mul1r.
  exact: (real_norm_change_bound hNZ a b).
exact: (@measurable_total_borel_postcomposition R X
  [the topologicalType of real_norm_metric_space hNZ]
  [the topologicalType of real_norm_metric_space hA] nu hnu f
  (fun z : real_norm_metric_space hNZ => (NZ z : real_norm_metric_space hA)) hfmeas
  (continuous_borel_function hc)).
Qed.

(** Source for [dgpr_norm_abs_bound]: | |f(y)| | <= M; blueprint
    def:heat. *)
Lemma dgpr_norm_abs_bound (y : X) : `|(NZ (f y) : R^o)| <= M.
Proof. by rewrite ger0_norm; [exact: hfM | exact: (real_seminorm_nonnegative hNZ.1)]. Qed.

(** Source for [dgpr_heat_norm_extension]: the heat extension of the
    scalar function |f| with respect to nu, that is
    [(s,x) |-> integral of p_s(x-y) |f(y)| d nu y]; blueprint
    lem:heat_extension(2),(3). *)
Definition dgpr_heat_norm_extension (s : R) (x : X) : R :=
  dgpr_heat_extension hnu hZ1 (fun y => (NZ (f y) : R^o)) s x.

(** Source for [dgpr_heat_norm_integral]: existence of the integral of
    [y |-> p_s(x-y) |f(y)|] with respect to nu (Federer 2.4.12 with
    2.4.9); blueprint lem:heat_extension(2),(3). *)
Theorem dgpr_heat_norm_integral (s : R) (x : X) : 0 < s ->
  is_measure_integral nu (real_total_integrand (fun y => p s (x - y) * NZ (f y)))
    (dgpr_heat_norm_extension s x)%:E.
Proof.
move=> hs.
exact: (dgpr_real_convolution_integral hnu hOpen hmass x dgpr_norm_measurable dgpr_norm_abs_bound
  (dgpr_kernel_class_zero hs) (fun z => dgpr_kernel_abs_le z hs)).
Qed.

(** Source for [dgpr_norm_total_integral]: existence of the integral of
    |f| with respect to nu (Federer 2.4.12 with 2.4.9); blueprint
    lem:heat_extension(3). *)
Theorem dgpr_norm_total_integral :
  exists b : R, is_measure_integral nu (real_total_integrand (fun y => NZ (f y))) b%:E.
Proof.
have hI : forall a : X, setT a -> norm_domain_interior N setT a by move=> a _; exact: dgpr_interior_setT.
have hk := norm_class_zero_constant hA (1 : R^o) hI.
have h1 : forall z : X, `|(fun _ : X => 1 : R) z| <= 1 by move=> z; rewrite normr1.
have h := dgpr_real_convolution_integral hnu hOpen hmass 0 dgpr_norm_measurable dgpr_norm_abs_bound hk h1.
eexists; apply: (measure_integral_graph_equivalent _ h) => y z.
by rewrite !real_total_integrand_graph mul1r.
Qed.

(** Source for [dgpr_heat_extension_zero_bound]: DPGPR 2026, section 3;
    blueprint lem:heat_extension(2), case j = 0, with c(n,0) = 1:
    |u_s(x)| <= integral of p_s(x-y) |f(y)| d nu y (Federer 2.4.12). *)
Theorem dgpr_heat_extension_zero_bound (s : R) (x : X) : 0 < s ->
  NZ (u s x) <= dgpr_heat_norm_extension s x.
Proof.
move=> hs.
have hI := dgpr_heat_extension_integral hnu hZ hOpen hmass hsep hfmeas hfM x hs.
apply: (total_vector_integral_almost_dominated_norm hnu hI (dgpr_heat_norm_integral x hs)).
apply: (measure_almost_everywhere_mono hnu _ (measure_almost_everywhere_true hnu)) => y _ /=.
by rewrite (real_seminorm_scale hNZ.1) ger0_norm // ltW // dgpr_kernel_gt0.
Qed.

Variable r : R.
Hypothesis hsupp : measure_almost_everywhere nu [set y | N y <= r].

(** Source for [dgpr_heat_extension_gauss_bound]: DPGPR 2026, section 3;
    blueprint lem:heat_extension(3), first inequality, with the existence of
    both integrals derived from the hypotheses of def:heat. *)
Theorem dgpr_heat_extension_gauss_bound (s : R) (x : X) : 0 < s ->
  exists b : R, is_measure_integral nu (real_total_integrand (fun y => NZ (f y))) b%:E /\
    dgpr_heat_norm_extension s x <=
      dgpr_kernel_constant n s * exp (- (Num.max (N x - r) 0) ^+ 2 / (4 * s)) * b.
Proof.
move=> hs; have [b hb] := dgpr_norm_total_integral.
exists b; split => //.
exact: (dgpr_heat_extension_gauss hnu hNZ hsupp hs (dgpr_heat_norm_integral x hs) hb).
Qed.

(** Source for [dgpr_heat_extension_first_bound]: DPGPR 2026, section 3;
    blueprint lem:heat_extension(2), case j = 1, with c(n,1) = 1/2:
    |D u_s(x)(v)| <= 2^(-1) s^(-1/2) (1 + (|x| + r) s^(-1/2)) |v| times
    the integral of p_s(x-y) |f(y)| d nu y. *)
Theorem dgpr_heat_extension_first_bound (s : R) (x v : X) : 0 < s ->
  NZ (conv (fun z => dgpr_kernel_differential s z v) x) <=
    2^-1 * (Num.sqrt s)^-1 * (1 + (N x + r) / Num.sqrt s) * dgpr_heat_norm_extension s x * N v.
Proof.
move=> hs.
have hI := dgpr_convolution_integral hnu hZ hOpen hmass hsep hfmeas hfM x
  (dgpr_kernel_first_class_zero v hs) (fun z => dgpr_kernel_differential_bound z v hs).
set C := 2^-1 * (Num.sqrt s)^-1 * (1 + (N x + r) / Num.sqrt s).
have hG := real_total_integral_scale hnu (C * N v) (dgpr_heat_norm_integral x hs).
rewrite mulrAC; apply: (total_vector_integral_almost_dominated_norm hnu hI hG).
apply: (measure_almost_everywhere_mono hnu _ hsupp) => y hy /=.
have hq : 0 < Num.sqrt s by rewrite sqrtr_gt0.
have hp := dgpr_kernel_gt0 (x - y) hs.
have hf0 := real_seminorm_nonnegative hNZ.1 (f y).
have hv0 := inner_norm_nonnegative (@euclidean_inner_productP R n) v.
rewrite (real_seminorm_scale hNZ.1).
apply: le_trans (ler_wpM2r hf0 (dgpr_kernel_first_scaled_bound (x - y) v hs)) _.
have hd : 1 + N (x - y) / Num.sqrt s <= 1 + (N x + r) / Num.sqrt s.
  by rewrite lerD2l ler_pM2r ?invr_gt0 //; exact: dgpr_distance_upper.
rewrite /C; move: (Num.sqrt s) hq hd => q hq hd; move: (p s (x - y)) hp => P hP.
set c := q^-1; have hc : 0 < c by rewrite invr_gt0.
move: (1 + N (x - y) * c) (1 + (N x + r) * c) hd => a b hab.
have -> : 2^-1 * c * a * P * N v * NZ (f y) = (2^-1 * c * P * N v * NZ (f y)) * a by ring.
have -> : 2^-1 * c * b * N v * (P * NZ (f y)) = (2^-1 * c * P * N v * NZ (f y)) * b by ring.
by apply: ler_wpM2l => //; rewrite !mulr_ge0 // ?invr_ge0 // ltW.
Qed.

(** Source for [dgpr_heat_extension_second_bound]: DPGPR 2026, section 3;
    blueprint lem:heat_extension(2), case j = 2, with c(n,2) = 1:
    |D^2 u_s(x)(v,w)| <= s^(-1) (1 + (|x| + r) s^(-1/2))^2 |v| |w| times
    the integral of p_s(x-y) |f(y)| d nu y. *)
Theorem dgpr_heat_extension_second_bound (s : R) (x v w : X) : 0 < s ->
  NZ (conv (fun z => dgpr_kernel_second s z v w) x) <=
    s^-1 * (1 + (N x + r) / Num.sqrt s) ^+ 2 * dgpr_heat_norm_extension s x * N v * N w.
Proof.
move=> hs.
have hI := dgpr_convolution_integral hnu hZ hOpen hmass hsep hfmeas hfM x
  (dgpr_kernel_second_class_zero v w hs) (fun z => dgpr_kernel_second_bound z v w hs).
set C := s^-1 * (1 + (N x + r) / Num.sqrt s) ^+ 2.
have hG := real_total_integral_scale hnu (C * N v * N w) (dgpr_heat_norm_integral x hs).
have -> : C * dgpr_heat_norm_extension s x * N v * N w = C * N v * N w * dgpr_heat_norm_extension s x.
  by move: (dgpr_heat_norm_extension s x) => D; ring.
apply: (total_vector_integral_almost_dominated_norm hnu hI hG).
apply: (measure_almost_everywhere_mono hnu _ hsupp) => y hy /=.
have hq : 0 < Num.sqrt s by rewrite sqrtr_gt0.
have hp := dgpr_kernel_gt0 (x - y) hs.
have hf0 := real_seminorm_nonnegative hNZ.1 (f y).
have hv0 := inner_norm_nonnegative (@euclidean_inner_productP R n) v.
have hw0 := inner_norm_nonnegative (@euclidean_inner_productP R n) w.
have hxy0 := inner_norm_nonnegative (@euclidean_inner_productP R n) (x - y).
rewrite (real_seminorm_scale hNZ.1).
apply: le_trans (ler_wpM2r hf0 (dgpr_kernel_second_scaled_bound (x - y) v w hs)) _.
have hd : 1 + N (x - y) / Num.sqrt s <= 1 + (N x + r) / Num.sqrt s.
  by rewrite lerD2l ler_pM2r ?invr_gt0 //; exact: dgpr_distance_upper.
have ha0 : 0 <= 1 + N (x - y) / Num.sqrt s by rewrite addr_ge0 // divr_ge0 // ltW.
have hsi : 0 < s^-1 by rewrite invr_gt0.
rewrite /C; move: (Num.sqrt s) hq hd ha0 => q hq hd ha0; move: (p s (x - y)) hp => P hP.
move: (1 + N (x - y) / q) (1 + (N x + r) / q) hd ha0 => a b hab ha0.
have hb0 : 0 <= b := le_trans ha0 hab.
have hab2 : a ^+ 2 <= b ^+ 2 by rewrite ler_sqr ?nnegrE.
move: (s^-1) hsi => t ht.
have -> : t * a ^+ 2 * P * N v * N w * NZ (f y) = (t * P * N v * N w * NZ (f y)) * a ^+ 2 by ring.
have -> : t * b ^+ 2 * N v * N w * (P * NZ (f y)) = (t * P * N v * N w * NZ (f y)) * b ^+ 2 by ring.
by apply: ler_wpM2l => //; rewrite !mulr_ge0 // ltW.
Qed.

End HeatBounds.
