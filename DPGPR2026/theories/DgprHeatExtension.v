(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3, heat
    extensions; blueprint dgpr_blueprint.tex, def:heat and
    lem:heat_extension(1),(3). For a measure nu over R^n, a complete normed
    space Z and f : R^n -> Z, the convolution of a kernel k : R^n -> R with
    f nu is the Federer vector integral (2.4.12) of [y |-> k(x-y) f(y)]
    with respect to nu, and the heat extension is the convolution with p_s.
    The differentiation under the integral sign rests on
    DgprParameterIntegralDifferential.v. The bounds of the heat kernel and
    of its first two derivatives used there are proved first. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm InnerNormInequalities PartialFunctionUP PartialFunctionBasic MeasureUP MeasureIntegralUP
  MeasureIntegralGraphEquivalence MeasureLpMembershipUP MeasureVectorIntegralUP MeasureVectorIntegral
  SummableRealFunctionUP CompleteMetricUP VectorDaniellHypotheses NormClassOneUP NormClassZeroTotalMeasurable
  MeasurableFunctionUP MeasurableScalarVectorProduct TotalVectorIntegralDomination FiniteMeasureBoundedNorm MeasureAlmostUP MeasureAlmostBasic MeasureIntegralComparison
  SummableRealArithmetic PartialExtendedOrderLoci
  NormDifferentialUP NormDifferentialLocal NormDifferentialLinear NormDifferentialArithmetic NormDifferentialChain
  NormClassZeroArithmetic NormClassZeroScalarProduct RealExponentialUP RealExponentialSealed CircularTrigonometrySealed.
From DPGPR Require Import DgprParameterIntegralDifferential DgprParameterIntegralSmooth DgprHeatKernel
  DgprHeatKernelDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section KernelBounds.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation B := (@euclidean_inner_product R n).
Local Notation exp := (@RealExponential.exponential R).
Local Notation p := (@dgpr_heat_kernel R n).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).

(** Source for [dgpr_class_zero_of_differential]: a map differentiable at
    every point of R^n is continuous (Federer 3.1.1); blueprint
    lem:heat_extension(1). *)
Lemma dgpr_class_zero_of_differential (k : X -> R) (Dk : X -> Hom X R^o) :
  (forall z, has_norm_differential N A1 setT k z (Dk z)) -> norm_class_zero N A1 setT k.
Proof.
move=> hk a _; split; first exact: dgpr_interior_setT.
exact: (norm_differential_continuous_at hA (hk a)).
Qed.

(** Source for [dgpr_kernel_constant]: the factor (4 pi s)^(-n/2) of
    p_s (blueprint def:heat and lem:kernel(6)). *)
Definition dgpr_kernel_constant (s : R) : R := Num.sqrt (4 * dgpr_pi R * s) ^- n.

(** Source for [dgpr_kernel_constant_ge0]: (4 pi s)^(-n/2) >= 0;
    blueprint lem:kernel(6). *)
Lemma dgpr_kernel_constant_ge0 (s : R) : 0 <= dgpr_kernel_constant s.
Proof. by rewrite /dgpr_kernel_constant invr_ge0 exprn_ge0 // sqrtr_ge0. Qed.

(** Source for [dgpr_kernel_abs_le]: |p_s(z)| <= (4 pi s)^(-n/2) for 0 < s;
    blueprint lem:kernel(6). *)
Lemma dgpr_kernel_abs_le (s : R) (z : X) : 0 < s -> `|p s z| <= dgpr_kernel_constant s.
Proof.
move=> hs; rewrite ger0_norm; first exact: (dgpr_kernel_max z hs).
exact: ltW (dgpr_kernel_gt0 z hs).
Qed.

(** Source for [dgpr_exp_neg_weight]: q exp(-q) <= 1 for 0 <= q, from
    1 + q <= exp(q); blueprint lem:kernel(4), case j <= 2. *)
Lemma dgpr_exp_neg_weight (q : R) : 0 <= q -> q * exp (- q) <= 1.
Proof.
move=> hq; have hp := real_exponential_positive (@RealExponential.laws R) q.
have h1 : exp (- q) * exp q = 1.
  by rewrite -(real_exponential_add (@RealExponential.laws R)) addNr
    (real_exponential_zero (@RealExponential.laws R)).
have -> : exp (- q) = (exp q)^-1.
  by apply: (mulIf (lt0r_neq0 hp)); rewrite h1 mulVf // lt0r_neq0.
rewrite ler_pdivrMr // mul1r; apply: le_trans (real_exponential_tangent (@RealExponential.laws R) q).
by rewrite lerDr.
Qed.

(** Source for [dgpr_kernel_sqr_weight]: |z|^2 p_s(z) <= 4s (4 pi s)^(-n/2);
    blueprint lem:kernel(4), case j <= 2. *)
Lemma dgpr_kernel_sqr_weight (s : R) (z : X) : 0 < s ->
  N z ^+ 2 * p s z <= 4 * s * dgpr_kernel_constant s.
Proof.
move=> hs; have h4 : 0 < 4 * s by rewrite mulr_gt0.
set q := N z ^+ 2 / (4 * s).
have hq : 0 <= q by rewrite divr_ge0 ?sqr_ge0 // ltW.
have e : N z ^+ 2 = 4 * s * q by rewrite /q mulrC divfK // lt0r_neq0.
rewrite /dgpr_heat_kernel (mulNr (N z ^+ 2)) -/q -/(dgpr_kernel_constant s) {1}e.
set c := dgpr_kernel_constant s.
have -> : 4 * s * q * (c * exp (- q)) = 4 * s * c * (q * exp (- q)) by ring.
rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l; last exact: dgpr_exp_neg_weight.
by apply: mulr_ge0; [exact: ltW | exact: dgpr_kernel_constant_ge0].
Qed.

(** Source for [dgpr_kernel_lin_weight]: |z| p_s(z) <= (1 + 4s)
    (4 pi s)^(-n/2); blueprint lem:kernel(4), case j = 1. *)
Lemma dgpr_kernel_lin_weight (s : R) (z : X) : 0 < s ->
  N z * p s z <= (1 + 4 * s) * dgpr_kernel_constant s.
Proof.
move=> hs; have hp := dgpr_kernel_gt0 z hs.
have hz : N z <= 1 + N z ^+ 2.
  have := sqr_ge0 (N z - 1 / 2); rewrite sqrrB expr2 => h; nra.
apply: le_trans (ler_wpM2r (ltW hp) hz) _.
rewrite mulrDl mul1r mulrDl mul1r; apply: lerD.
  exact: dgpr_kernel_max.
exact: dgpr_kernel_sqr_weight.
Qed.

(** Source for [dgpr_kernel_differential_bound]: a uniform bound of
    D p_s(z)(v) by a multiple of |v|; blueprint lem:kernel(4), case j = 1,
    in the uniform form used for lem:heat_extension(1). *)
Lemma dgpr_kernel_differential_bound (s : R) (z v : X) : 0 < s ->
  `|dgpr_kernel_differential s z v| <=
    (2 * s)^-1 * ((1 + 4 * s) * dgpr_kernel_constant s) * N v.
Proof.
move=> hs; have hp := dgpr_kernel_gt0 z hs.
have h2 : 0 < (2 * s)^-1 by rewrite invr_gt0 mulr_gt0.
rewrite dgpr_kernel_differentialE normrM (gtr0_norm hp) normrM normrN (gtr0_norm h2) -!mulrA.
apply: ler_wpM2l; first exact: ltW.
have hc := inner_cauchy (@euclidean_inner_productP R n) z v.
have h3 : `|B z v| * p s z <= N z * N v * p s z.
  by rewrite ler_wpM2r // ltW.
apply: le_trans h3 _.
rewrite mulrAC (mulrA (1 + 4 * s)); apply: ler_wpM2r; first exact: (inner_norm_nonnegative (@euclidean_inner_productP R n)).
exact: dgpr_kernel_lin_weight.
Qed.

(** Source for [dgpr_kernel_second_bound]: a uniform bound of
    D^2 p_s(z)(v,w) by a multiple of |v| |w|; blueprint lem:kernel(4), case
    j = 2, in the uniform form used for lem:heat_extension(1). *)
Lemma dgpr_kernel_second_bound (s : R) (z v w : X) : 0 < s ->
  `|dgpr_kernel_second s z v w| <=
    ((4 * s ^+ 2)^-1 * (4 * s * dgpr_kernel_constant s) + (2 * s)^-1 * dgpr_kernel_constant s) *
    N v * N w.
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
set c := dgpr_kernel_constant s.
have -> : (a * N z ^+ 2 * (N v * N w) + b * (N v * N w)) * p s z =
  (a * (N z ^+ 2 * p s z) + b * p s z) * (N v * N w) by ring.
rewrite -mulrA; apply: ler_wpM2r; first by rewrite mulr_ge0.
apply: lerD; apply: ler_wpM2l => //.
  exact: dgpr_kernel_sqr_weight.
exact: dgpr_kernel_max.
Qed.

(** Source for [dgpr_inner_class_zero]: continuity of [z |-> z . v];
    blueprint lem:heat_extension(1). *)
Lemma dgpr_inner_class_zero (v : X) : norm_class_zero N A1 setT (fun z : X => B z v).
Proof.
have -> : (fun z : X => B z v) = dgpr_inner_hom v.
  by apply: funext => z; rewrite dgpr_inner_homE euclidean_inner_symmetric.
apply: (@dgpr_class_zero_of_differential _ (fun _ => dgpr_inner_hom v)) => z.
apply: (norm_differential_linear hN hA (dgpr_interior_setT z)).
exact: dgpr_inner_hom_bounded.
Qed.

(** Source for [dgpr_kernel_class_zero]: continuity of p_s; blueprint
    lem:heat_extension(1). *)
Lemma dgpr_kernel_class_zero (s : R) : 0 < s -> norm_class_zero N A1 setT (p s).
Proof.
move=> hs; apply: (@dgpr_class_zero_of_differential _ (dgpr_kernel_differential s)) => z.
exact: dgpr_kernel_differential_formula.
Qed.

(** Source for [dgpr_kernel_first_class_zero]: continuity of
    [z |-> D p_s(z)(v)]; blueprint lem:heat_extension(1). *)
Lemma dgpr_kernel_first_class_zero (s : R) (v : X) : 0 < s ->
  norm_class_zero N A1 setT (fun z => dgpr_kernel_differential s z v).
Proof.
move=> hs; apply: (@dgpr_class_zero_of_differential _ (fun z => dgpr_kernel_second s z v)) => z.
exact: dgpr_kernel_second_formula.
Qed.

(** Source for [dgpr_kernel_second_class_zero]: continuity of
    [z |-> D^2 p_s(z)(v,w)]; blueprint lem:heat_extension(1). *)
Lemma dgpr_kernel_second_class_zero (s : R) (v w : X) : 0 < s ->
  norm_class_zero N A1 setT (fun z => dgpr_kernel_second s z v w).
Proof.
move=> hs.
have hI : forall a, setT a -> norm_domain_interior N setT a by move=> a _; exact: dgpr_interior_setT.
have h1 := norm_class_zero_scale hA ((4 * s ^+ 2)^-1) (dgpr_inner_class_zero v).
have h2 := norm_class_zero_scalar_product hA h1 (dgpr_inner_class_zero w).
have h3 := norm_class_zero_constant hA ((2 * s)^-1 * B v w : R^o) hI.
have h4 := norm_class_zero_subtract hA h2 h3.
have h5 := norm_class_zero_scalar_product hA h4 (dgpr_kernel_class_zero hs).
have -> : (fun z => dgpr_kernel_second s z v w) =
  (fun z : X => ((((4 * s ^+ 2)^-1 *: (B z v : R^o)) *: (B z w : R^o) -
    ((2 * s)^-1 * B v w : R^o)) *: (p s z : R^o) : R^o)).
  by apply: funext => z; rewrite dgpr_kernel_secondE.
exact: h5.
Qed.

End KernelBounds.

Section Convolution.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Variable nu : set X -> \bar R.
Hypothesis hnu : is_measure nu.
Variable Z : lmodType R.
Variable NZ : Z -> R.
Hypothesis hNZ : is_real_norm NZ.
Hypothesis hZ : is_complete_metric_space (real_norm_metric_space hNZ).
Variable f : X -> Z.
Local Notation has_integral := (@dgpr_has_integral R X nu Z NZ hNZ).

(** Source for [dgpr_convolution]: the integral of
    [y |-> k(x-y) f(y)] with respect to nu in the sense of Federer 2.4.12,
    and 0 when this function is not nu summable; blueprint def:heat and
    lem:heat_extension(1), where k is p_s or one of its derivatives. *)
Definition dgpr_convolution (k : X -> R) (x : X) : Z :=
  match pselect (is_measure_lp_function nu 1
    (partial_function_total (fun y => (k (x - y) *: f y : real_norm_metric_space hNZ)))) with
  | left h => measure_vector_integral hZ hnu h
  | right _ => 0
  end.

(** Source for [dgpr_heat_extension]: DPGPR 2026, section 3; blueprint
    def:heat, u(s,x) = integral of p_s(x-y) f(y) d nu y. *)
Definition dgpr_heat_extension (s : R) (x : X) : Z := dgpr_convolution (@dgpr_heat_kernel R n s) x.

(** Source for [dgpr_convolution_spec]: the convolution is the integral
    whenever the latter exists (uniqueness, Federer 2.4.12); blueprint
    def:heat. *)
Lemma dgpr_convolution_spec (k : X -> R) (x : X) (z : Z) :
  has_integral (fun y => k (x - y) *: f y) z -> dgpr_convolution k x = z.
Proof.
move=> h; rewrite /dgpr_convolution; case: pselect => [hl|hn]; last by case: (hn h.1).
exact: (measure_vector_integral_unique (measure_vector_integral_specification hZ hnu hl) h).
Qed.

(** Source for [dgpr_setT_and]: bookkeeping of the whole-space domain in
    the chain rule of Federer 3.1.11; blueprint lem:heat_extension(1). *)
Lemma dgpr_setT_and (Y : Type) (g : X -> Y) : (fun x : X => setT x /\ setT (g x)) = setT.
Proof. by apply: funext => x; apply: propext; split. Qed.



(** Source for [dgpr_reflect_class_zero]: continuity of [y |-> k(x-y)];
    blueprint def:heat. *)
Lemma dgpr_reflect_class_zero (k : X -> R) (x : X) :
  norm_class_zero N A1 setT k -> norm_class_zero N A1 (fun _ => True) (fun y => k (x - y)).
Proof.
move=> hk a _; split; first exact: dgpr_interior_setT.
move=> e he; have [_ hc] := hk (x - a) I; have [d [hd hd']] := hc e he.
exists d; split => // h _ hh.
have e1 : x - (a + h) = x - a + - h by rewrite opprD addrA.
rewrite e1; apply: hd' => //.
by rewrite (inner_normN (@euclidean_inner_productP R n)).
Qed.

Section Hypotheses.
Hypothesis hOpen : forall A : set X, @open (real_norm_metric_space hN) A -> measure_measurable nu A.
Variable m : R.
Hypothesis hmass : nu setT = m%:E.
Hypothesis hsep : is_separable_normed_space hNZ.
Hypothesis hfmeas : is_measure_measurable_function nu
  (partial_function_total (fun y => (f y : real_norm_metric_space hNZ))).
Variable M : R.
Hypothesis hfM : forall y, NZ (f y) <= M.

(** Source for [dgpr_constant_integral]: the integral of a constant c with
    respect to the finite measure nu is c nu(R^n); blueprint
    lem:heat_extension(1). *)
Lemma dgpr_constant_integral (c : R) :
  is_measure_integral nu (real_total_integrand (fun _ : X => c)) (c * m)%:E.
Proof.
apply: (measure_integral_graph_equivalent _ (finite_measure_constant_integral hnu c hmass)).
by move=> x y; rewrite real_total_integrand_graph; split => h.
Qed.

(** Source for [dgpr_constant_summable]: constants are nu summable;
    blueprint lem:heat_extension(1). *)
Lemma dgpr_constant_summable (c : R) : summable_real_functions nu (fun _ : X => c).
Proof. by exists (c * m); exact: dgpr_constant_integral. Qed.

(** Source for [dgpr_convolution_integral]: for a bounded continuous
    kernel k the function [y |-> k(x-y) f(y)] is nu summable and its integral
    is the convolution (Federer 2.4.12 with the dominated existence of
    2.4.9); blueprint def:heat. *)
Lemma dgpr_convolution_integral (k : X -> R) (K : R) (x : X) :
  norm_class_zero N A1 setT k -> (forall z, `|k z| <= K) ->
  has_integral (fun y => k (x - y) *: f y) (dgpr_convolution k x).
Proof.
move=> hk hK.
have hka := norm_class_zero_scalar_real_measurable hnu hOpen (dgpr_reflect_class_zero x hk).
have hmeas := measurable_scalar_vector_product hnu hsep hka hfmeas.
have hb y : NZ (k (x - y) *: f y) <= K * M.
  rewrite (real_seminorm_scale hNZ.1) ler_pM //; first exact: (real_seminorm_nonnegative hNZ.1).
have [z [hz _]] := dominated_total_vector_integral_exists hZ hnu hsep hmeas
  (dgpr_constant_integral (K * M)) hb.
by rewrite (dgpr_convolution_spec hz).
Qed.

(** Source for [dgpr_translation_differential]: the differential of
    [x |-> x - y] is the identity; blueprint lem:heat_extension(1). *)
Lemma dgpr_translation_differential (y b : X) :
  has_norm_differential N N setT (fun x : X => x - y) b (@dgpr_identity_hom R n).
Proof.
have hI : has_norm_differential N N setT (@dgpr_identity_hom R n) b (@dgpr_identity_hom R n).
  apply: (norm_differential_linear hN hN (dgpr_interior_setT b)).
  by exists 1; split => // h; rewrite mul1r.
have hC := norm_differential_constant hN hN (- y) (dgpr_interior_setT b).
have h := norm_differential_add hN hI hC.
by rewrite addr0 in h.
Qed.

(** Source for [dgpr_line_differential]: the differential of the linear
    map [t |-> t c]; blueprint lem:heat_extension(1). *)
Lemma dgpr_line_differential (c : Z) (t : R^o) :
  has_norm_differential A1 NZ setT (dgpr_line_hom c) t (dgpr_line_hom c).
Proof.
apply: (norm_differential_linear hA hNZ); first by exists 1; split => //; exact: ltr01.
exists (NZ c); split; first exact: (real_seminorm_nonnegative hNZ.1).
by move=> h; rewrite dgpr_line_homE (real_seminorm_scale hNZ.1) mulrC.
Qed.

(** Source for [dgpr_kernel_translate_differential]: the differential of
    [x |-> k(x-y) f(y)] (chain rule, Federer 3.1.11); blueprint
    lem:heat_extension(1). *)
Lemma dgpr_kernel_translate_differential (k : X -> R) (Dk : X -> Hom X R^o) (y b : X) :
  (forall z, has_norm_differential N A1 setT k z (Dk z)) ->
  has_norm_differential N NZ setT (fun x : X => k (x - y) *: f y) b
    (hom_comp (dgpr_line_hom (f y)) (hom_comp (Dk (b - y)) (@dgpr_identity_hom R n))).
Proof.
move=> hk.
have h1 := norm_differential_chain hN hN hA (dgpr_translation_differential y b) (hk (b - y)).
rewrite dgpr_setT_and in h1.
have h2 := norm_differential_chain hN hA hNZ h1 (dgpr_line_differential (f y) (k (b - y))).
by rewrite dgpr_setT_and in h2.
Qed.

(** Source for [dgpr_convolution_differential]: differentiation under the
    integral sign for convolutions with a bounded kernel of class 1 whose
    derivative is bounded and continuous; blueprint lem:heat_extension(1),
    proof. *)
Theorem dgpr_convolution_differential (k : X -> R) (Dk : X -> Hom X R^o) (K K1 : R) (x : X) :
  (forall z, has_norm_differential N A1 setT k z (Dk z)) ->
  (forall z, `|k z| <= K) ->
  (forall v, norm_class_zero N A1 setT (fun z => Dk z v)) ->
  (forall z v, `|Dk z v| <= K1 * N v) ->
  exists L : Hom X Z, has_norm_differential N NZ setT (dgpr_convolution k) x L /\
    forall v, L v = dgpr_convolution (fun z => Dk z v) x.
Proof.
move=> hk hK hDk hK1.
have hk0 := dgpr_class_zero_of_differential hk.
have hint x' := dgpr_convolution_integral x' hk0 hK.
have hDint v := dgpr_convolution_integral x (hDk v) (fun z => hK1 z v).
have [L hL] := @dgpr_integral_hom_exists R X nu hnu X Z NZ hNZ
  (fun y => hom_comp (dgpr_line_hom (f y)) (hom_comp (Dk (x - y)) (@dgpr_identity_hom R n)))
  (fun v => ex_intro _ _ (hDint v)).
exists L; split; last first.
  by move=> v; apply/esym/dgpr_convolution_spec; exact: hL.
apply: (@dgpr_parameter_integral_differential R X nu hnu X Z N NZ hN hNZ setT
  (fun x' y => k (x' - y) *: f y)
  (fun x' y => hom_comp (dgpr_line_hom (f y)) (hom_comp (Dk (x' - y)) (@dgpr_identity_hom R n)))
  (fun _ => K1 * M) (dgpr_convolution k) L x 1 ltr01) => //.
- by move=> h y _; exact: dgpr_kernel_translate_differential.
- exact: dgpr_constant_summable.
move=> h y v _.
change (NZ (Dk (x + h - y) v *: f y) <= K1 * M * N v).
rewrite (real_seminorm_scale hNZ.1) mulrAC; apply: ler_pM.
- exact: normr_ge0.
- exact: (real_seminorm_nonnegative hNZ.1).
- exact: hK1.
- exact: hfM.
Qed.

(** Source for [dgpr_heat_extension_integral]: DPGPR 2026, section 3;
    blueprint def:heat, existence of the integral defining u(s,x). *)
Theorem dgpr_heat_extension_integral (s : R) (x : X) : 0 < s ->
  has_integral (fun y => @dgpr_heat_kernel R n s (x - y) *: f y) (dgpr_heat_extension s x).
Proof.
move=> hs; exact: (dgpr_convolution_integral x (dgpr_kernel_class_zero hs)
  (fun z => dgpr_kernel_abs_le z hs)).
Qed.

(** Source for [dgpr_heat_extension_first]: DPGPR 2026, section 3;
    blueprint lem:heat_extension(1), case j = 1: D u_s(x)(v) is the integral
    of D p_s(x-y)(v) f(y) d nu y. *)
Theorem dgpr_heat_extension_first (s : R) (x : X) : 0 < s ->
  exists L : Hom X Z, has_norm_differential N NZ setT (dgpr_heat_extension s) x L /\
    forall v, L v = dgpr_convolution (fun z => @dgpr_kernel_differential R n s z v) x.
Proof.
move=> hs; exact: (dgpr_convolution_differential x
  (fun z => dgpr_kernel_differential_formula z hs) (fun z => dgpr_kernel_abs_le z hs)
  (fun v => dgpr_kernel_first_class_zero v hs) (fun z v => dgpr_kernel_differential_bound z v hs)).
Qed.

(** Source for [dgpr_heat_extension_second]: DPGPR 2026, section 3;
    blueprint lem:heat_extension(1), case j = 2: D^2 u_s(x)(v,w) is the
    integral of D^2 p_s(x-y)(v,w) f(y) d nu y. *)
Theorem dgpr_heat_extension_second (s : R) (v x : X) : 0 < s ->
  exists L : Hom X Z,
    has_norm_differential N NZ setT
      (dgpr_convolution (fun z => @dgpr_kernel_differential R n s z v)) x L /\
    forall w, L w = dgpr_convolution (fun z => @dgpr_kernel_second R n s z v w) x.
Proof.
move=> hs.
apply: (dgpr_convolution_differential (K1 :=
  ((4 * s ^+ 2)^-1 * (4 * s * dgpr_kernel_constant n s) + (2 * s)^-1 * dgpr_kernel_constant n s) * N v)
  x (fun z => dgpr_kernel_second_formula z v hs) (fun z => dgpr_kernel_differential_bound z v hs)
  (fun w => dgpr_kernel_second_class_zero v w hs)).
by move=> z w; exact: dgpr_kernel_second_bound.
Qed.

Variable r : R.
Hypothesis hsupp : measure_almost_everywhere nu [set y | N y <= r].

(** Source for [dgpr_integral_le_on_ball]: monotonicity of the integral
    (Federer 2.4.4) for an inequality holding on the closed ball B(0,r),
    which carries nu; blueprint lem:heat_extension(3). *)
Lemma dgpr_integral_le_on_ball (g1 g2 : X -> R) (a b : R) :
  is_measure_integral nu (real_total_integrand g1) a%:E ->
  is_measure_integral nu (real_total_integrand g2) b%:E ->
  (forall y, N y <= r -> g1 y <= g2 y) -> a <= b.
Proof.
move=> h1 h2 hle.
have h := measure_integral_monotone hnu h1 h2
  (measure_almost_everywhere_mono hnu _ hsupp).
rewrite -lee_fin; apply: h => y hy.
exists (g1 y)%:E, (g2 y)%:E; split; first by apply/real_total_integrand_graph.
by split; [apply/real_total_integrand_graph | rewrite lee_fin; exact: hle].
Qed.

(** Source for [dgpr_distance_lower]: max{|x| - r, 0} <= |x - y| for
    |y| <= r; blueprint lem:heat_extension(3), proof. *)
Lemma dgpr_distance_lower (x y : X) : N y <= r -> Num.max (N x - r) 0 <= N (x - y).
Proof.
move=> hy; have hN0 := inner_norm_nonnegative (@euclidean_inner_productP R n) (x - y).
rewrite ge_max hN0 andbT lerBlDr.
have := inner_norm_triangle (@euclidean_inner_productP R n) (x - y) y.
by rewrite subrK => h; apply: le_trans h _; rewrite lerD2l.
Qed.

(** Source for [dgpr_distance_upper]: |x - y| <= |x| + r for |y| <= r;
    blueprint lem:heat_extension(3), proof. *)
Lemma dgpr_distance_upper (x y : X) : N y <= r -> N (x - y) <= N x + r.
Proof.
move=> hy; apply: le_trans (inner_norm_triangle (@euclidean_inner_productP R n) x (- y)) _.
by rewrite (inner_normN (@euclidean_inner_productP R n)) lerD2l.
Qed.

(** Source for [dgpr_heat_extension_gauss]: DPGPR 2026, section 3;
    blueprint lem:heat_extension(3), first inequality: the integral of
    p_s(x-y) |f(y)| d nu y is at most (4 pi s)^(-n/2)
    exp(-max{|x| - r, 0}^2/(4s)) times the integral of |f| d nu. *)
Theorem dgpr_heat_extension_gauss (s : R) (x : X) (a b : R) : 0 < s ->
  is_measure_integral nu (real_total_integrand (fun y => @dgpr_heat_kernel R n s (x - y) * NZ (f y))) a%:E ->
  is_measure_integral nu (real_total_integrand (fun y => NZ (f y))) b%:E ->
  a <= dgpr_kernel_constant n s * RealExponential.exponential (- (Num.max (N x - r) 0) ^+ 2 / (4 * s)) * b.
Proof.
move=> hs ha hb.
have hb' := real_total_integral_scale hnu
  (dgpr_kernel_constant n s * RealExponential.exponential (- (Num.max (N x - r) 0) ^+ 2 / (4 * s))) hb.
apply: (dgpr_integral_le_on_ball ha hb') => y hy.
apply: ler_wpM2r; first exact: (real_seminorm_nonnegative hNZ.1).
rewrite /dgpr_heat_kernel -/(dgpr_kernel_constant n s); apply: ler_wpM2l.
  exact: dgpr_kernel_constant_ge0.
apply: dgpr_exponential_le; rewrite !mulNr lerN2; apply: ler_wpM2r.
  by rewrite invr_ge0 ltW // mulr_gt0.
have hm0 : 0 <= Num.max (N x - r) 0 by rewrite le_max lexx orbT.
have hd := dgpr_distance_lower x hy.
have hN0 := inner_norm_nonnegative (@euclidean_inner_productP R n) (x - y).
by rewrite ler_sqr.
Qed.

End Hypotheses.
End Convolution.
