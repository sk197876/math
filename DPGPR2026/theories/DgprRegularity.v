(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3;
    blueprint dgpr_blueprint.tex, lem:regularity: S has Gaussian decay
    before T; B, eta, kappa, q, log S, log rho and log q have polynomial
    growth before T; rho log q and rho |B|^2 have Gaussian decay before T.

    The proof follows the blueprint. On a strip a <= t <= b of Omega_T
    with b < T the joint bounds of DgprBackwardHeatDecay.v give
    ||D^j F|| <= c (1 + |x|)^K P_(T-t)|f| for the heat extensions
    F = U, W, R, Psi, rho, and P_(T-t)|f| is at most a constant times U,
    R or rho. Hence the derivatives of U, W, R, Psi, rho and S are
    bounded by weights c (1 + |x|)^c phi with phi = U, R, rho and S
    respectively (DgprRegularityWeights.v). Products of such weights are
    weights relative to products, so the derivatives of S^(-1) have
    weights relative to S^(-1), those of B = S^(-1) W, eta = S^(-1) Psi,
    kappa and q relative to S^(-1) U <= 1, S^(-1) R <= (T - b)^(-1/2),
    and q <= 1. The derivatives of log F = F^(-1) DF are bounded by
    weights relative to F^(-1) F = 1, and |log F| has polynomial growth
    by the Gaussian lower bound of lem:heat_extension(3) and the upper
    bound of F given by the Gaussian decay of U and R.

    The exponents of the polynomial weights are not computed: the
    statements of def:classes only assert their existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LinearBasis HomInner ScalarInnerProduct
  ProductInner CompleteMetricUP VectorDaniellHypotheses PartialFunctionUP PartialFunctionBasic MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP MeasureIntegralComparison
  SummableRealFunctionUP SummableRealArithmetic RadonMeasureUP ScalarNormMetricCompleteness
  SmoothFunctionSpaceUP SmoothTestSpaces NormDifferentialUP NormClassOneUP NormClassHigherUP
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearZero NormBoundedBilinearUP
  NormHigherDifferentialUP NormRegularity NormRegularityOperations NormRegularityBilinear
  ScalarNormalizationRegularity RealExponentialUP RealExponentialSealed RealExponentialLaws
  InnerNormalizationSmooth LocalUniquenessExample.
From DPGPR Require Import DgprGrowthClasses DgprWeightedBilinear DgprRegularityWeights DgprClassesProduct
  DgprHeatKernel DgprHeatKernelFamily DgprHeatExtension DgprHeatExtensionBounds DgprHeatSemiconvex
  DgprBackwardHeat DgprBackwardHeatDecay DgprStanding DgprHeatObjects DgprIdentities
  DgprIdentitiesDivergence DgprMeasureComparison DgprIdentitiesSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section ScalarBounds.
Variable R : realType.
Local Notation E := (@RealExponential.exponential R).
Local Notation LOG := (@RealExponential.logarithm R).
Local Notation hE := (@RealExponential.laws R).

(** Source for [dgpr_log_abs_le]: for 0 < l <= F <= c,
    |log F| <= |log c| + |log l|, since the logarithm is increasing
    (Federer 2.4.12, p. 86); proof of lem:regularity. *)
Lemma dgpr_log_abs_le (F l c : R) : 0 < l -> l <= F -> F <= c -> `|LOG F| <= `|LOG c| + `|LOG l|.
Proof.
move=> hl hlF hFc.
have hF : 0 < F := lt_le_trans hl hlF.
have hc : 0 < c := lt_le_trans hF hFc.
have h1 : LOG l <= LOG F by rewrite real_logarithm_order.
have h2 : LOG F <= LOG c by rewrite real_logarithm_order.
have h3 := ler_norm (LOG c).
have h4 : - LOG l <= `|LOG l| by rewrite -normrN ler_norm.
have h5 := normr_ge0 (LOG l); have h6 := normr_ge0 (LOG c).
case: (lerP 0 (LOG F)) => hs.
- by rewrite ger0_norm //; lra.
- by rewrite ltr0_norm //; lra.
Qed.

(** Source for [dgpr_log_gaussian_le]: |log(k exp(-y^2/s))| <=
    |log k| + y^2/s for 0 < k and 0 < s (Federer 2.4.12, p. 86); proof of
    lem:regularity. *)
Lemma dgpr_log_gaussian_le (k y s : R) : 0 < k -> 0 < s ->
  `|LOG (k * E (- y ^+ 2 / s))| <= `|LOG k| + y ^+ 2 / s.
Proof.
move=> hk hs.
rewrite real_logarithm_product // ?(real_exponential_positive hE) // (real_logarithm_exponential hE).
apply: le_trans (ler_normD _ _) _.
by rewrite lerD2l mulNr normrN ger0_norm // divr_ge0 // ?sqr_ge0 // ltW.
Qed.

(** Source for [dgpr_quadratic_polynomial]: C0 + C1 (y + r)^2 is at most
    the weight c (1 + y)^c of def:classes for a suitable c; proof of
    lem:regularity. *)
Lemma dgpr_quadratic_polynomial (C0 C1 r y : R) : 0 <= C0 -> 0 <= C1 -> 0 <= r -> 0 <= y ->
  C0 + C1 * (y + r) ^+ 2 <= dgpr_polynomial_weight (C0 + C1 * (1 + r) ^+ 2 + 1 + 2%:R) y.
Proof.
move=> h0 h1 hr hy.
have hP : 0 <= C1 * (1 + r) ^+ 2 by rewrite mulr_ge0 // sqr_ge0.
have hc : 0 < C0 + C1 * (1 + r) ^+ 2 + 1 by lra.
apply: le_trans (dgpr_polynomial_power_le 2 hc hy).
have hy1 : 1 <= (1 + y) ^+ 2 by rewrite sqrrD expr1n; have := sqr_ge0 y; nra.
have hyr : (y + r) ^+ 2 <= (1 + r) ^+ 2 * (1 + y) ^+ 2.
  rewrite -exprMn; apply: lerXn2r; rewrite ?nnegrE; try nra.
have hA := ler_wpM2l h0 hy1; have hB := ler_wpM2l h1 hyr.
have hY : 0 <= (1 + y) ^+ 2 by exact: sqr_ge0.
rewrite mulr1 in hA; nra.
Qed.

(** Source for [dgpr_log_polynomial]: if k exp(-(y + r)^2/s) <= F <= c,
    then |log F| is at most a weight c' (1 + y)^c' of def:classes; proof
    of lem:regularity. *)
Lemma dgpr_log_polynomial (F c k s r y : R) : 0 < k -> 0 < s -> 0 <= r -> 0 <= y ->
  k * E (- (y + r) ^+ 2 / s) <= F -> F <= c ->
  `|LOG F| <= dgpr_polynomial_weight (`|LOG c| + `|LOG k| + s^-1 * (1 + r) ^+ 2 + 1 + 2%:R) y.
Proof.
move=> hk hs hr hy hlF hFc.
have hl : 0 < k * E (- (y + r) ^+ 2 / s) by rewrite mulr_gt0 // (real_exponential_positive hE).
apply: le_trans (dgpr_log_abs_le hl hlF hFc) _.
have h0 : 0 <= `|LOG c| + `|LOG k| by rewrite addr_ge0.
have hs1 : 0 <= s^-1 by rewrite invr_ge0 ltW.
apply: le_trans _ (dgpr_quadratic_polynomial h0 hs1 hr hy).
have := dgpr_log_gaussian_le (y + r) hk hs.
by rewrite [s^-1 * _]mulrC; lra.
Qed.

(** Source for [dgpr_gaussian_weight_scale]: m c exp(-y^2/c) <=
    (m + 1) c exp(-y^2/((m + 1) c)) for 0 <= m and 0 < c; supporting
    lem:regularity. *)
Lemma dgpr_gaussian_weight_scale (m c y : R) : 0 <= m -> 0 < c ->
  m * dgpr_gaussian_weight c y <= dgpr_gaussian_weight ((m + 1) * c) y.
Proof.
move=> hm hc; rewrite /dgpr_gaussian_weight.
have hmc : 0 <= (m + 1) * c by rewrite mulr_ge0 // ?ltW //; lra.
have hE1 := real_exponential_positive hE (- y ^+ 2 / c).
have hle : E (- y ^+ 2 / c) <= E (- y ^+ 2 / ((m + 1) * c)).
  rewrite real_exponential_order; apply: dgpr_gaussian_exponent_monotone => //.
  by rewrite ler_peMl //; lra.
have := ler_wpM2l hmc hle; have := mulr_ge0 (ltW hc) (ltW hE1); nra.
Qed.

(** Source for [dgpr_gaussian_weight_le]: c exp(-y^2/c) <= c for 0 < c;
    supporting lem:regularity. *)
Lemma dgpr_gaussian_weight_le (c y : R) : 0 < c -> dgpr_gaussian_weight c y <= c.
Proof.
move=> hc; rewrite /dgpr_gaussian_weight.
rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l; first exact: ltW.
rewrite -(real_exponential_zero hE) real_exponential_order mulNr oppr_le0.
by rewrite divr_ge0 // ?sqr_ge0 // ltW.
Qed.

(** Source for [dgpr_scalar_mul_flip_bilinear]: [(s,t) |-> t s] is a
    bounded bilinear map R x R -> R (Federer 1.10.5); supporting
    lem:regularity. *)
Lemma dgpr_scalar_mul_flip_bilinear :
  norm_bounded_bilinear (fun t : R^o => `|t|) (fun t : R^o => `|t|) (fun t : R^o => `|t|)
    (fun s t : R^o => t * s : R^o).
Proof.
split.
- split.
  + by move=> v a s t /=; change (v * (a * s + t) = a * (v * s) + v * t); ring.
  + by move=> s a v w /=; change ((a * v + w) * s = a * (v * s) + w * s); ring.
- exists 1; split; first exact: ler01.
  by move=> s t; rewrite mul1r normrM mulrC.
Qed.
End ScalarBounds.

Section ZeroOrder.
Variable R : realType.
Variable n : nat.
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BT := (product_inner_productP (scalar_inner_productP R) (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm BT).
Local Notation hNT := (inner_norm_real_norm BT).
Variables (Z : lmodType R) (NZ : Z -> R).
Hypothesis hNZ : is_real_norm NZ.

(** Source for [dgpr_derivative_bounded_zero]: the differential of order
    0 of f at p is f(p) (Federer 3.1.11, p. 219), so a bound of order 0 is
    a bound of |f|; supporting lem:regularity. *)
Lemma dgpr_derivative_bounded_zero (A K0 : set TX) (f : TX -> Z) (w : TX -> R) :
  dgpr_derivative_bounded hNT hNZ A K0 f 0 w -> forall p, K0 p -> A p -> NZ (f p) <= w p.
Proof.
move=> hb p hp hpA.
have hZ0 := @ContinuousMultilinear.laws R 0 TX Z NT NZ hNT hNZ.
have [z hz] := continuous_multilinear_zero_surjective hNZ hZ0 (f p).
have hD : dgpr_higher_differential hNT hNZ A f 0 p z by split.
apply: le_trans _ (hb p z hp hD).
by rewrite (continuous_multilinear_zero_norm hNZ hZ0) hz.
Qed.
End ZeroOrder.

Section RelativeCalculus.
Variable R : realType.
Variable n : nat.
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BT := (product_inner_productP (scalar_inner_productP R) (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm BT).
Local Notation hNT := (inner_norm_real_norm BT).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation LOG := (@RealExponential.logarithm R).
Variables T a b : R.
Hypothesis hbT : b < T.
Local Notation OmT := (dgpr_before T).
Local Notation K0 := (dgpr_time_strip a b).
Local Notation C phi := (dgpr_relative_class a b phi).
Local Notation WD Y NY hNY := (dgpr_weighted_derivative NT OmT K0
  (fun j => @ContinuousMultilinear.evaluation R j TX Y NT NY hNT hNY)
  (fun j => @ContinuousMultilinear.norm R j TX Y NT NY hNT hNY)).
Local Notation WDA := (WD R^o A1 hA).

(** Source for [dgpr_relative_bilinear]: if the derivatives of f and g
    have weights relative to phi1 and phi2 and phi1 phi2 <= phi3, then
    those of [p |-> B(f(p), g(p))] have weights relative to phi3, by the
    Leibniz formula (Federer 3.1.11, p. 220); proof of lem:regularity. *)
Lemma dgpr_relative_bilinear (U V W : lmodType R) (NU : U -> R) (NV : V -> R) (NW : W -> R)
    (hNU : is_real_norm NU) (hNV : is_real_norm NV) (hNW : is_real_norm NW)
    (B : U -> V -> W) (phi1 phi2 phi3 : TX -> R) (f : TX -> U) (g : TX -> V) :
  norm_bounded_bilinear NU NV NW B ->
  (forall p, K0 p -> [/\ 0 <= phi1 p, 0 <= phi2 p & phi1 p * phi2 p <= phi3 p]) ->
  norm_class_all_orders hNT hNU OmT f -> norm_class_all_orders hNT hNV OmT g ->
  (forall j, WD U NU hNU (C phi1) f j) -> (forall j, WD V NV hNV (C phi2) g j) ->
  forall j, WD W NW hNW (C phi3) (fun p => B (f p) (g p)) j.
Proof.
move=> hB hphi hf hg hbf hbg.
have h3 p : K0 p -> 0 <= phi3 p.
  by move=> hp; have [h1 h2 h12] := hphi p hp; exact: le_trans (mulr_ge0 h1 h2) h12.
exact: (dgpr_weighted_product hNW hB (dgpr_relative_product hphi) (dgpr_relative_sum h3) hf hg hbf hbg).
Qed.

(** Source for [dgpr_relative_weaken]: a weight relative to phi is a
    weight relative to psi when 0 <= phi <= M psi on the strip; proof of
    lem:regularity. *)
Lemma dgpr_relative_weaken (Y : lmodType R) (NY : Y -> R) (hNY : is_real_norm NY)
    (f : TX -> Y) (phi psi : TX -> R) (M : R) :
  0 <= M -> (forall p, K0 p -> 0 <= psi p /\ phi p <= M * psi p) ->
  forall j, WD Y NY hNY (C phi) f j -> WD Y NY hNY (C psi) f j.
Proof. by move=> hM hphi j; apply: dgpr_weighted_mono; exact: (dgpr_relative_dominate hM hphi). Qed.

(** Source for [dgpr_relative_reciprocal]: blueprint lem:regularity,
    proof: if F > 0 on Omega_T is of class infinity and the derivatives
    of F have weights relative to F on the strip, then those of F^(-1)
    have weights relative to F^(-1); induction on the order with
    D(F^(-1)) = -F^(-2) DF (DgprRegularityWeights.v). *)
Lemma dgpr_relative_reciprocal (F : TX -> R^o) :
  (forall p, OmT p -> 0 < F p) -> norm_class_all_orders hNT hA OmT F ->
  (forall j, WDA (C F) F j) -> forall j, WDA (C (fun p => (F p)^-1)) (fun p => (F p)^-1) j.
Proof.
move=> hF0 hF hb.
have hpos p : K0 p -> 0 < F p by move=> hp; exact: hF0 p (dgpr_strip_before hbT hp).
have hi p : K0 p -> 0 <= (F p)^-1 by move=> hp; rewrite invr_ge0 ltW // hpos.
have h11 := @dgpr_relative_product R n a b (fun p => (F p)^-1) (fun p => (F p)^-1)
  (fun p => (F p)^-1 * (F p)^-1) (fun p hp => And3 (hi p hp) (hi p hp) (lexx _)).
have h21 : forall p, K0 p -> [/\ 0 <= (F p)^-1 * (F p)^-1, 0 <= F p & (F p)^-1 * (F p)^-1 * F p <= (F p)^-1].
  move=> p hp; split; [exact: mulr_ge0 (hi p hp) (hi p hp) | exact: ltW (hpos p hp) |].
  by rewrite -mulrA mulVf ?mulr1 // gt_eqF // hpos.
have hs1 := @dgpr_relative_sum R n a b (fun p => (F p)^-1) hi.
have hs2 := @dgpr_relative_sum R n a b (fun p => (F p)^-1 * (F p)^-1) (fun p hp => mulr_ge0 (hi p hp) (hi p hp)).
have [w [hw hle]] := @dgpr_relative_self R n a b (fun p => (F p)^-1) hi.
have h0 : WDA (C (fun p => (F p)^-1)) (fun p => (F p)^-1) 0.
  apply: (dgpr_weighted_zero hNT hA hw) => p hp _.
  by rewrite ger0_norm; [exact: hle p hp | exact: hi p hp].
have hF0' x : OmT x -> F x != 0 by move=> hx; rewrite gt_eqF // hF0.
exact: (dgpr_weighted_reciprocal h11 (dgpr_relative_product h21) hs1 hs2 hF0' hF hb h0).
Qed.

(** Source for [dgpr_relative_logarithm]: blueprint lem:regularity,
    proof: D log F = F^(-1) DF, so if the derivatives of F have weights
    relative to F and |log F| has polynomial growth on the strip, then
    the derivatives of log F have weights relative to F^(-1) F = 1. *)
Lemma dgpr_relative_logarithm (F : TX -> R^o) (c : R) :
  (forall p, OmT p -> 0 < F p) -> norm_class_all_orders hNT hA OmT F ->
  (forall j, WDA (C F) F j) -> 0 < c ->
  (forall p, K0 p -> `|LOG (F p)| <= dgpr_polynomial_weight c (N p.2)) ->
  forall j, WDA (C (fun _ => 1)) (fun p => LOG (F p) : R^o) j.
Proof.
move=> hF0 hF hb hc hlog.
have hpos p : K0 p -> 0 < F p by move=> hp; exact: hF0 p (dgpr_strip_before hbT hp).
have hm := dgpr_relative_reciprocal hF0 hF hb.
have h10 : forall p, K0 p -> [/\ 0 <= (F p)^-1, 0 <= F p & (F p)^-1 * F p <= 1].
  move=> p hp; have h := hpos p hp.
  by split; [rewrite invr_ge0 ltW | exact: ltW | rewrite mulVf // gt_eqF].
have hs0 := @dgpr_relative_sum R n a b (fun _ => 1) (fun _ _ => ler01).
have h0 : WDA (C (fun _ => 1)) (fun p => LOG (F p) : R^o) 0.
  apply: (dgpr_weighted_zero hNT hA (w := fun p => dgpr_polynomial_weight c (N p.2) * 1)).
    exact: dgpr_relative_weight hc (fun _ _ => ler01).
  by move=> p hp _; rewrite mulr1; exact: hlog p hp.
exact: (dgpr_weighted_logarithm (dgpr_relative_product h10) hs0 hF0 hF hb hm h0).
Qed.
End RelativeCalculus.

Section Conversion.
Variable R : realType.
Variable n : nat.
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BT := (product_inner_productP (scalar_inner_productP R) (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm BT).
Local Notation hNT := (inner_norm_real_norm BT).
Variables (Z : lmodType R) (NZ : Z -> R).
Hypothesis hNZ : is_real_norm NZ.
Variable T : R.
Local Notation WD a b := (dgpr_weighted_derivative NT (dgpr_before T) (dgpr_time_strip a b)
  (fun j => @ContinuousMultilinear.evaluation R j TX Z NT NZ hNT hNZ)
  (fun j => @ContinuousMultilinear.norm R j TX Z NT NZ hNT hNZ)).

(** Source for [dgpr_relative_polynomial_growth]: weights relative to 1
    on every strip a <= t <= b with b < T give polynomial growth before T
    (def:classes); proof of lem:regularity. *)
Lemma dgpr_relative_polynomial_growth (f : TX -> Z) :
  norm_class_all_orders hNT hNZ (dgpr_before T) f ->
  (forall a b, b < T -> forall j, WD a b (dgpr_relative_class a b (fun _ => 1)) f j) ->
  dgpr_polynomial_growth_before hNZ T f.
Proof.
move=> hf hb; split => // j a b hbT.
have [w [hw hwb]] := hb a b hbT j.
have [c [hc hle]] := dgpr_relative_polynomial hw.
by exists c; split => // p z hp hz; exact: le_trans (hwb p z hp hz) (hle p hp).
Qed.

(** Source for [dgpr_relative_gaussian_decay]: weights relative to a
    function phi with Gaussian decay on every strip give Gaussian decay
    before T (def:classes and the proof of lem:classes); proof of
    lem:regularity. *)
Lemma dgpr_relative_gaussian_decay (f : TX -> Z) :
  norm_class_all_orders hNT hNZ (dgpr_before T) f ->
  (forall a b, b < T -> exists phi c0, [/\ 0 < c0,
    forall p, dgpr_time_strip a b p -> phi p <= dgpr_gaussian_weight c0 (N p.2) &
    forall j, WD a b (dgpr_relative_class a b phi) f j]) ->
  dgpr_gaussian_decay_before hNZ T f.
Proof.
move=> hf hb; split => // j a b hbT.
have [phi [c0 [hc0 hphi hj]]] := hb a b hbT.
have [w [hw hwb]] := hj j.
have [c [hc hle]] := dgpr_relative_gaussian hc0 hphi hw.
by exists c; split => // p z hp hz; exact: le_trans (hwb p z hp hz) (hle p hp).
Qed.
End Conversion.

Section HeatRatio.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BT := (product_inner_productP (scalar_inner_productP R) (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm BT).
Local Notation hNT := (inner_norm_real_norm BT).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation hZ1 := (@scalar_norm_metric_complete R).
Local Notation E := (@RealExponential.exponential R).
Local Notation hE := (@RealExponential.laws R).
Local Notation p := (@dgpr_heat_kernel R n).
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
Variable r : R.
Hypothesis hsupp : measure_almost_everywhere nu [set y | N y <= r].
Hypothesis hr : 0 <= r.
Variable T : R.
Local Notation u1 := (dgpr_heat_extension hnu hZ1 (fun _ : X => 1 : R^o)).
Local Notation hne := (@dgpr_heat_norm_extension R n nu hnu Z NZ f).
Local Notation F := (dgpr_backward_heat hnu hZ f T).

(** Source for [dgpr_heat_unit_nonnegative]: the heat extension of
    (nu, 1) is nonnegative (lem:heat_extension(3)); supporting
    lem:regularity. *)
Lemma dgpr_heat_unit_nonnegative (s : R) (x : X) : 0 < s -> 0 <= u1 s x.
Proof.
move=> hs.
have h := dgpr_heat_norm_extension_ge0 hnu hZ1 hOpen hmass (scalar_norm_separable R) (dgpr_one_measurable hnu)
  (@dgpr_one_bound1 R n) x hs.
have e : (fun y : X => (`|(1 : R^o)| : R^o)) = (fun _ : X => 1 : R^o) by apply: funext => y; rewrite normr1.
have e' : @dgpr_heat_norm_extension R n nu hnu R^o (fun t : R^o => `|t|) (fun _ : X => 1 : R^o) s x = u1 s x.
  by rewrite /dgpr_heat_norm_extension /= e.
by rewrite -e'.
Qed.

(** Source for [dgpr_heat_norm_unit_le]: the heat extension of |f| is at
    most M times that of 1 when |f| <= M (Federer 2.4.12); proof of
    lem:regularity. *)
Lemma dgpr_heat_norm_unit_le (s : R) (x : X) : 0 < s -> hne s x <= M * u1 s x.
Proof.
move=> hs.
have hn := dgpr_heat_norm_integral hnu hOpen hmass hfmeas hfM x hs.
have hu := real_total_integral_scale hnu M (dgpr_unit_kernel_integral hnu hOpen hmass x hs).
rewrite -lee_fin; apply: (measure_integral_monotone hnu hn hu).
apply: (measure_almost_everywhere_mono hnu _ (measure_almost_everywhere_true hnu)) => y _.
exists (p s (x - y) * NZ (f y))%:E, (M * p s (x - y))%:E.
split; first by apply/real_total_integrand_graph.
split; first by apply/real_total_integrand_graph.
rewrite lee_fin [M * _]mulrC; apply: ler_wpM2l; first exact: ltW (dgpr_kernel_gt0 _ hs).
exact: hfM.
Qed.

(** Source for [dgpr_heat_ratio]: blueprint lem:regularity, proof: on a
    strip a <= t <= b with b < T the derivatives of
    F(t,x) = u(T - t, x) are bounded by c (1 + |x|)^K times the heat
    extension of |f| (DgprBackwardHeatDecay.v), which is at most M times
    the heat extension of (nu, 1); hence they have weights relative to
    [(t,x) |-> u_1(T - t, x)]. *)
Theorem dgpr_heat_ratio (a b : R) : b < T ->
  forall j, dgpr_weighted_derivative NT (dgpr_before T) (dgpr_time_strip a b)
    (fun k => @ContinuousMultilinear.evaluation R k TX Z NT NZ hNT hNZ)
    (fun k => @ContinuousMultilinear.norm R k TX Z NT NZ hNT hNZ)
    (dgpr_relative_class a b (fun q : TX => u1 (T - q.1) q.2)) F j.
Proof.
move=> hbT j.
have [c [K [hc hbd]]] := dgpr_backward_heat_joint_bound hnu hZ hOpen hmass hsep hfmeas hfM hsupp hr j a hbT.
have hM : 0 <= Num.max M 0 by rewrite le_max lexx orbT.
have hphi (q : TX) : dgpr_time_strip a b q -> [/\ 0 <= u1 (T - q.1) q.2, 0 <= hne (T - q.1) q.2 &
    hne (T - q.1) q.2 <= Num.max M 0 * u1 (T - q.1) q.2].
  move=> hq; have hs : 0 < T - q.1 by rewrite subr_gt0; exact: (dgpr_strip_before hbT hq).
  have hu := dgpr_heat_unit_nonnegative q.2 hs.
  split => //; first exact: (dgpr_heat_norm_extension_ge0 hnu hZ hOpen hmass hsep hfmeas hfM q.2 hs).
  apply: le_trans (dgpr_heat_norm_unit_le q.2 hs) _; apply: ler_wpM2r => //.
  by rewrite le_max lexx.
have [w [hw hle]] := dgpr_relative_joint (phi := fun q : TX => u1 (T - q.1) q.2)
  (h := fun q : TX => hne (T - q.1) q.2) K hM hc hphi.
by exists w; split => // q D hq hD; exact: le_trans (hbd q D hq hD) (hle q hq).
Qed.

(** Source for [dgpr_heat_unit_lower]: blueprint lem:heat_extension(3),
    second inequality, on a strip a <= t <= b with b < T: the heat
    extension of (nu, 1) at (T - t, x) is at least
    (4 pi (T - a))^(-n/2) m exp(-(|x| + r)^2/(4 (T - b))); proof of
    lem:regularity. *)
Lemma dgpr_heat_unit_lower (a b : R) (q : TX) : b < T -> 0 <= m -> dgpr_time_strip a b q ->
  dgpr_kernel_constant n (T - a) * m * E (- (N q.2 + r) ^+ 2 / (4 * (T - b))) <= u1 (T - q.1) q.2.
Proof.
move=> hbT hm hq; have hs : 0 < T - q.1 by rewrite subr_gt0; exact: (dgpr_strip_before hbT hq).
have [haq hqb] : a <= q.1 /\ q.1 <= b by apply/andP.
have hb : is_measure_integral nu (real_total_integrand (fun _ : X => (1 : R^o))) m%:E.
  by have := dgpr_constant_integral hnu hmass 1; rewrite mul1r.
have hl := dgpr_heat_extension_lower hnu hOpen hmass hsupp (g := fun _ => 1 : R^o) (M := 1) q.2 hs
  (dgpr_one_measurable hnu) (@dgpr_one_bound1 R n) (fun _ => ler01) hb.
apply: le_trans hl.
have hTb : 0 < T - b by rewrite subr_gt0.
have hk := dgpr_kernel_constant_antitone n hs (_ : T - q.1 <= T - a).
have hk0 := dgpr_kernel_constant_ge0 n (T - a).
have hex : E (- (N q.2 + r) ^+ 2 / (4 * (T - b))) <= E (- (N q.2 + r) ^+ 2 / (4 * (T - q.1))).
  rewrite real_exponential_order; apply: dgpr_gaussian_exponent_monotone; first by rewrite mulr_gt0.
  by rewrite ler_wpM2l // lerD2l lerN2.
have hE0 := ltW (real_exponential_positive hE (- (N q.2 + r) ^+ 2 / (4 * (T - b)))).
rewrite mulrAC; apply: ler_wpM2r => //.
by apply: ler_pM => //; apply: hk; rewrite lerD2l lerN2.
Qed.
End HeatRatio.

(** Source for [dgpr_kernel_constant_gt0]: (4 pi s)^(-n/2) > 0 for s > 0;
    supporting lem:regularity. *)
Lemma dgpr_kernel_constant_gt0 (R : realType) (n : nat) (s : R) : 0 < s -> 0 < dgpr_kernel_constant n s.
Proof.
by move=> hs; rewrite /dgpr_kernel_constant invr_gt0 exprn_gt0 // sqrtr_gt0 mulr_gt0 // mulr_gt0 // dgpr_pi_gt0.
Qed.

Section Regularity.
Variable R : realType.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Local Notation BT := (product_inner_productP (scalar_inner_productP R) (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm BT).
Local Notation hNT := (inner_norm_real_norm BT).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation LOG := (@RealExponential.logarithm R).
Local Notation E := (@RealExponential.exponential R).
Local Notation hE := (@RealExponential.laws R).
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
Variable Es : lmodType R.
Variable ev : Es -> X -> Y.
Hypothesis hEs : is_smooth_function_space hN hNY setT ev.
Variable Ups : Hom (smooth_test_space hEs) R^o.
Variable ups : set (real_norm_metric_space hN) -> \bar R.
Variable dups : X -> Hom Y R^o.
Variable delta : R.
Variable T : R.
Variable mu0 : set X -> \bar R.
Variable gamma : R.
Hypothesis hS : dgpr_standing heY hm K lam Lam mu r0 Xf Ups ups dups delta T mu0 gamma.
Local Notation hmu := (dgpr_standing_mu_measure hS).
Local Notation hups := (dgpr_standing_ups_measure hS).
Local Notation hmu0 := (dgpr_standing_mu0_measure hS).
Local Notation hOmu := (dgpr_standing_mu_borel hS).
Local Notation hOups := (radon_open_measurable (dgpr_standing_ups_radon hS)).
Local Notation hOmu0 := (dgpr_standing_mu0_borel hS).
Local Notation hMmu := (dgpr_standing_mu_mass hS).
Local Notation hMups := (dgpr_standing_ups_mass hS).
Local Notation hMmu0 := (dgpr_standing_mu0_mass hS).
Local Notation U := (dgpr_heat_U hS).
Local Notation W := (dgpr_heat_W hS).
Local Notation Rr := (dgpr_heat_R hS).
Local Notation Psi := (dgpr_heat_Psi hS).
Local Notation S := (dgpr_heat_S hS).
Local Notation rho := (dgpr_heat_rho hS).
Local Notation B := (dgpr_heat_B hS).
Local Notation eta := (dgpr_heat_eta hS).
Local Notation kappa := (dgpr_heat_kappa hS).
Local Notation Q := (dgpr_heat_q hS).
Local Notation OmT := (dgpr_before T).

Let hr0 : 0 <= r0 := ltW (dgpr_standing_r0 hS).
Let hsmu := dgpr_standing_mu_support hS.
Let hsups := dgpr_identities_spt hS.
Let hsmu0 := dgpr_standing_mu0_support hS.

Let hUpos (q : TX) : OmT q -> 0 < U q.
Proof. by case: q => t x ht; exact: (dgpr_identities_U_pos hS x ht). Qed.

Let hSpos (q : TX) : OmT q -> 0 < S q.
Proof. by case: q => t x ht; exact: (dgpr_identities_S_pos hS x ht). Qed.

Let hrhopos (q : TX) : OmT q -> 0 < rho q.
Proof. by case: q => t x ht; exact: (dgpr_identities_rho_pos hS x ht). Qed.

Let hR0 (q : TX) : OmT q -> 0 <= Rr q.
Proof. by case: q => t x ht; exact: (dgpr_identities_R_ge0 hS x ht). Qed.

Let hUS (q : TX) : OmT q -> U q <= S q.
Proof. by case: q => t x ht; exact: (dgpr_identities_U_le_S hS x ht). Qed.

Let hrhoU (q : TX) : OmT q -> rho q <= U q.
Proof. by case: q => t x ht; exact: (dgpr_identities_rho_le_U hS x ht). Qed.

Section Strip.
Variables a b : R.
Hypothesis hbT : b < T.
Local Notation K0 := (dgpr_time_strip a b).
Local Notation C phi := (dgpr_relative_class a b phi).
Local Notation WD Y NY hNY := (dgpr_weighted_derivative NT OmT K0
  (fun j => @ContinuousMultilinear.evaluation R j TX Y NT NY hNT hNY)
  (fun j => @ContinuousMultilinear.norm R j TX Y NT NY hNT hNY)).
Local Notation WDA := (WD R^o A1 hA).
Local Notation WDH := (WD (Hom X Y) (inner_norm BH) hNH).
Local Notation WDD := (WD (Hom Y R^o) (inner_norm BD) hND).
Local Notation rt := (fun p : TX => Num.sqrt (T - p.1) : R^o).
Local Notation irt := (fun p : TX => (Num.sqrt (T - p.1))^-1 : R^o).
Local Notation Mb := ((Num.sqrt (T - b))^-1).

Let hOm (q : TX) : K0 q -> OmT q.
Proof. by move=> hq; change (q.1 < T); case/andP: hq => _ hqb; exact: le_lt_trans hqb hbT. Qed.

Let hMb : 0 <= Mb.
Proof. by rewrite invr_ge0 sqrtr_ge0. Qed.

Let hRS (q : TX) : K0 q -> Rr q <= Mb * S q.
Proof.
move=> hq; have hq' := hOm hq.
have [_ hqb] : a <= q.1 /\ q.1 <= b by apply/andP.
have hsb : 0 < Num.sqrt (T - b) by rewrite sqrtr_gt0 subr_gt0.
have hst : Num.sqrt (T - b) <= Num.sqrt (T - q.1).
  by apply: ler_wsqrtr; rewrite lerD2l lerN2.
have e : Rr q = Mb * (Num.sqrt (T - b) * Rr q) by rewrite mulrA mulVf ?mul1r // gt_eqF.
rewrite {1}e; apply: ler_wpM2l; first exact: hMb.
have := ler_wpM2r (hR0 hq') hst; have := ltW (hUpos hq').
change (S q) with (U q + Num.sqrt (T - q.1) * Rr q); lra.
Qed.

(** Source for [dgpr_regularity_U_ratio]: proof of lem:regularity,
    ||D^j U|| <= c (1 + |x|)^K U on the strip. *)
Lemma dgpr_regularity_U_ratio (j : nat) : WDA (C (fun q => U q)) U j.
Proof.
exact: (dgpr_heat_ratio hmu hZ1 hOmu hMmu hsep1 (dgpr_one_measurable hmu) (@dgpr_one_bound1 R n)
  hsmu hr0 a hbT j).
Qed.

(** Source for [dgpr_regularity_W_ratio]: proof of lem:regularity,
    ||D^j W|| <= c (1 + |x|)^K U on the strip, since |X| <= Lambda. *)
Lemma dgpr_regularity_W_ratio (j : nat) : WDH (C (fun q => U q)) W j.
Proof.
exact: (dgpr_heat_ratio hmu hHc hOmu hMmu hHs (dgpr_standing_X_measurable hS)
  (fun y => dgpr_standing_K_norm hS (dgpr_standing_X_values hS y)) hsmu hr0 a hbT j).
Qed.

(** Source for [dgpr_regularity_R_ratio]: proof of lem:regularity,
    ||D^j R|| <= c (1 + |x|)^K R on the strip. *)
Lemma dgpr_regularity_R_ratio (j : nat) : WDA (C (fun q => Rr q)) Rr j.
Proof.
exact: (dgpr_heat_ratio hups hZ1 hOups hMups hsep1 (dgpr_one_measurable hups) (@dgpr_one_bound1 R n)
  hsups hr0 a hbT j).
Qed.

(** Source for [dgpr_regularity_Psi_ratio]: proof of lem:regularity,
    ||D^j Psi|| <= c (1 + |x|)^K R on the strip, since
    ||dUpsilon|| <= 1. *)
Lemma dgpr_regularity_Psi_ratio (j : nat) : WDD (C (fun q => Rr q)) Psi j.
Proof.
exact: (dgpr_heat_ratio hups hDc hOups hMups hDs (dgpr_standing_dups_measurable hS)
  (dgpr_standing_dups_bound hS) hsups hr0 a hbT j).
Qed.

(** Source for [dgpr_regularity_rho_ratio]: proof of lem:regularity,
    ||D^j rho|| <= c (1 + |x|)^K rho on the strip. *)
Lemma dgpr_regularity_rho_ratio (j : nat) : WDA (C (fun q => rho q)) rho j.
Proof.
exact: (dgpr_heat_ratio hmu0 hZ1 hOmu0 hMmu0 hsep1 (dgpr_one_measurable hmu0) (@dgpr_one_bound1 R n)
  hsmu0 hr0 a hbT j).
Qed.

(** Source for [dgpr_regularity_S_ratio]: proof of lem:regularity,
    ||D^j S|| <= c (1 + |x|)^c S on the strip: S = U + (T - t)^(1/2) R,
    the derivatives of (T - t)^(1/2) are bounded on the strip
    (DgprRegularityWeights.v), and R <= (T - b)^(-1/2) S there. *)
Lemma dgpr_regularity_S_ratio (j : nat) : WDA (C (fun q => S q)) S j.
Proof.
have [hU _ hR _ _] := dgpr_identities_smooth_extensions hS.
have [hh _] := dgpr_time_root_class n T.
have h1R (q : TX) : K0 q -> [/\ 0 <= (1 : R), 0 <= Rr q & 1 * Rr q <= Rr q].
  by move=> hq; split; [exact: ler01 | exact: hR0 (hOm hq) | rewrite mul1r].
have hhR := dgpr_relative_bilinear hA (dgpr_scalar_mul_bilinear R) (phi1 := fun _ => 1)
  (phi2 := fun q => Rr q) (phi3 := fun q => Rr q) h1R hh hR (dgpr_time_root_bound n a hbT)
  dgpr_regularity_R_ratio.
have hS0 (q : TX) : K0 q -> 0 <= S q by move=> hq; exact: ltW (hSpos (hOm hq)).
have hS1 := dgpr_relative_weaken (psi := fun q => S q) hMb (fun q hq => conj (hS0 q hq) (hRS hq)) (hhR j).
have hUS1 (q : TX) : K0 q -> 0 <= S q /\ U q <= 1 * S q.
  by move=> hq; split; [exact: hS0 | rewrite mul1r; exact: hUS (hOm hq)].
have hU1 := dgpr_relative_weaken ler01 hUS1 (dgpr_regularity_U_ratio j).
have h := dgpr_weighted_add (dgpr_relative_sum hS0) (hU j) (norm_class_scalar_product (hh j) (hR j)) hU1 hS1.
exact h.
Qed.

(** Source for [dgpr_regularity_S_inverse_ratio]: proof of
    lem:regularity, ||D^j (S^(-1))|| <= c (1 + |x|)^c S^(-1) on the strip,
    by induction with D(S^(-1)) = -S^(-2) DS. *)
Lemma dgpr_regularity_S_inverse_ratio (j : nat) :
  WDA (C (fun q => (S q)^-1)) (fun q => (S q)^-1 : R^o) j.
Proof.
exact: (dgpr_relative_reciprocal hbT hSpos (dgpr_identities_smooth_S hS) dgpr_regularity_S_ratio j).
Qed.

(** Source for [dgpr_regularity_Q_ratio]: proof of lem:regularity,
    ||D^j q|| <= c (1 + |x|)^c q on the strip, for q = rho S^(-1). *)
Lemma dgpr_regularity_Q_ratio (j : nat) : WDA (C (fun q => Q q)) Q j.
Proof.
have [_ _ _ _ hr] := dgpr_identities_smooth_extensions hS.
have hph (q : TX) : K0 q -> [/\ 0 <= rho q, 0 <= (S q)^-1 & rho q * (S q)^-1 <= Q q].
  move=> hq; have hq' := hOm hq.
  by split; [exact: ltW (hrhopos hq') | rewrite invr_ge0 ltW // hSpos | exact: lexx].
exact: (dgpr_relative_bilinear hA (dgpr_scalar_mul_bilinear R) hph hr (dgpr_heat_S_inverse_smooth hS)
  dgpr_regularity_rho_ratio dgpr_regularity_S_inverse_ratio j).
Qed.

(** Source for [dgpr_regularity_S_gaussian_bound]: on the strip,
    S <= c0 exp(-|x|^2/c0), from the Gaussian decay of U and R
    (DgprIdentitiesSmooth.v) and (T - t)^(1/2) <= (T - a)^(1/2). *)
Lemma dgpr_regularity_S_gaussian_bound :
  exists c0, 0 < c0 /\ forall q, K0 q -> S q <= dgpr_gaussian_weight c0 (N q.2).
Proof.
have [[_ hUb] _ [_ hRb] _ _] := dgpr_regularity_gaussian_extensions hS.
have [c1 [hc1 hU1]] := hUb 0%N a b hbT.
have [c2 [hc2 hR1]] := hRb 0%N a b hbT.
have hsa : 0 <= Num.sqrt (T - a) := sqrtr_ge0 _.
have hc2' : 0 < (Num.sqrt (T - a) + 1) * c2 by rewrite mulr_gt0 // ltr_wpDl.
exists (c1 + (Num.sqrt (T - a) + 1) * c2); split; first exact: addr_gt0.
move=> q hq; have hq' := hOm hq.
have hUq := dgpr_derivative_bounded_zero hU1 hq hq'.
have hRq := dgpr_derivative_bounded_zero hR1 hq hq'.
apply: le_trans (dgpr_gaussian_weight_sum _ hc1 hc2').
change (U q + Num.sqrt (T - q.1) * Rr q <= dgpr_gaussian_weight c1 (N q.2) +
  dgpr_gaussian_weight ((Num.sqrt (T - a) + 1) * c2) (N q.2)).
apply: lerD; first exact: le_trans (ler_norm _) hUq.
apply: le_trans (dgpr_gaussian_weight_scale (N q.2) hsa hc2).
apply: ler_pM; [exact: sqrtr_ge0 | exact: hR0 hq' | | exact: le_trans (ler_norm _) hRq].
by apply: ler_wsqrtr; case/andP: hq => haq _; rewrite lerD2l lerN2.
Qed.

(** Source for [dgpr_strip_log_bound]: if
    (4 pi (T - a))^(-n/2) M exp(-(|x| + r0)^2/(4 (T - b))) <= F <= c1 on
    the strip, then |log F| <= c (1 + |x|)^c there; proof of
    lem:regularity. *)
Lemma dgpr_strip_log_bound (F : TX -> R) (M c1 : R) : 0 < M ->
  (forall q, K0 q -> dgpr_kernel_constant n (T - a) * M * E (- (N q.2 + r0) ^+ 2 / (4 * (T - b))) <= F q) ->
  (forall q, K0 q -> F q <= c1) ->
  exists c, 0 < c /\ forall q, K0 q -> `|LOG (F q)| <= dgpr_polynomial_weight c (N q.2).
Proof.
move=> hM hlow hup.
case: (lerP a b) => hab; last first.
  by exists 1; split => // q /andP [h1 h2]; exfalso; lra.
have hTb : 0 < T - b by rewrite subr_gt0.
have hTa : 0 < T - a by rewrite subr_gt0; exact: le_lt_trans hab hbT.
set k := dgpr_kernel_constant n (T - a) * M.
have hk : 0 < k by rewrite /k mulr_gt0 // dgpr_kernel_constant_gt0.
have hs : 0 < 4 * (T - b) by rewrite mulr_gt0.
exists (`|LOG c1| + `|LOG k| + (4 * (T - b))^-1 * (1 + r0) ^+ 2 + 1 + 2%:R); split.
  have := normr_ge0 (LOG c1); have := normr_ge0 (LOG k).
  have : 0 <= (4 * (T - b))^-1 * (1 + r0) ^+ 2 by rewrite mulr_ge0 ?sqr_ge0 // invr_ge0 ltW.
  lra.
move=> q hq.
exact: (dgpr_log_polynomial hk hs hr0 (inner_norm_nonnegative _ _) (hlow q hq) (hup q hq)).
Qed.

(** Source for [dgpr_regularity_log_bounds]: blueprint lem:regularity,
    proof: on the strip |log S|, |log rho| and |log q| are at most
    c (1 + |x|)^c, by the Gaussian lower bounds of U and rho of
    lem:heat_extension(3), rho <= U <= S and the upper bound
    S <= c0 exp(-|x|^2/c0). *)
Lemma dgpr_regularity_log_bounds :
  [/\ exists c, 0 < c /\ forall q, K0 q -> `|LOG (S q)| <= dgpr_polynomial_weight c (N q.2),
      exists c, 0 < c /\ forall q, K0 q -> `|LOG (rho q)| <= dgpr_polynomial_weight c (N q.2) &
      exists c, 0 < c /\ forall q, K0 q -> `|LOG (Q q)| <= dgpr_polynomial_weight c (N q.2)].
Proof.
have [c0 [hc0 hSg]] := dgpr_regularity_S_gaussian_bound.
have hga := dgpr_standing_gamma hS.
have hSc (q : TX) : K0 q -> S q <= c0.
  by move=> hq; exact: le_trans (hSg q hq) (dgpr_gaussian_weight_le _ hc0).
have hUl (q : TX) : K0 q -> dgpr_kernel_constant n (T - a) * 1 *
    E (- (N q.2 + r0) ^+ 2 / (4 * (T - b))) <= U q.
  by move=> hq; exact: (dgpr_heat_unit_lower hmu hOmu hMmu hsmu hbT ler01 hq).
have hrl (q : TX) : K0 q -> dgpr_kernel_constant n (T - a) * gamma *
    E (- (N q.2 + r0) ^+ 2 / (4 * (T - b))) <= rho q.
  by move=> hq; exact: (dgpr_heat_unit_lower hmu0 hOmu0 hMmu0 hsmu0 hbT (ltW hga) hq).
split.
- apply: (dgpr_strip_log_bound ltr01 _ hSc) => q hq.
  exact: le_trans (hUl q hq) (hUS (hOm hq)).
- apply: (dgpr_strip_log_bound hga hrl) => q hq.
  exact: le_trans (le_trans (hrhoU (hOm hq)) (hUS (hOm hq))) (hSc q hq).
- have hM : 0 < gamma * c0^-1 by rewrite mulr_gt0 ?invr_gt0.
  apply: (dgpr_strip_log_bound (c1 := 1) hM) => q hq; have hq' := hOm hq; have hSq := hSpos hq'.
  + change (dgpr_kernel_constant n (T - a) * (gamma * c0^-1) *
      E (- (N q.2 + r0) ^+ 2 / (4 * (T - b))) <= rho q * (S q)^-1).
    rewrite mulrA mulrAC; apply: ler_pM.
    * rewrite mulr_ge0 // ?mulr_ge0 ?dgpr_kernel_constant_ge0 ?ltW //.
      exact: (real_exponential_positive hE).
    * by rewrite invr_ge0 ltW.
    * exact: hrl q hq.
    * by rewrite lef_pV2 ?posrE //; exact: hSc q hq.
  + change (rho q / S q <= 1); rewrite ler_pdivrMr // mul1r.
    exact: le_trans (hrhoU hq') (hUS hq').
Qed.

(** Source for [dgpr_regularity_B_ratio]: proof of lem:regularity,
    ||D^j B|| <= c (1 + |x|)^c on the strip: B = S^(-1) W with weights
    relative to S^(-1) and U, and S^(-1) U <= 1. *)
Lemma dgpr_regularity_B_ratio (j : nat) : WDH (C (fun _ => 1)) B j.
Proof.
have [_ hW _ _ _] := dgpr_identities_smooth_extensions hS.
have hph (q : TX) : K0 q -> [/\ 0 <= (S q)^-1, 0 <= U q & (S q)^-1 * U q <= 1].
  move=> hq; have hq' := hOm hq; have hSq := hSpos hq'.
  split; [by rewrite invr_ge0 ltW | exact: ltW (hUpos hq') |].
  by rewrite mulrC ler_pdivrMr // mul1r; exact: hUS hq'.
have h := dgpr_relative_bilinear hNH (dgpr_scalar_vector_bilinear hNH) hph (dgpr_heat_S_inverse_smooth hS) hW
  dgpr_regularity_S_inverse_ratio dgpr_regularity_W_ratio j.
exact h.
Qed.

(** Source for [dgpr_regularity_eta_ratio]: proof of lem:regularity,
    ||D^j eta|| <= c (1 + |x|)^c on the strip: eta = S^(-1) Psi with
    weights relative to S^(-1) and R, and S^(-1) R <= (T - b)^(-1/2). *)
Lemma dgpr_regularity_eta_ratio (j : nat) : WDD (C (fun _ => 1)) eta j.
Proof.
have [_ _ _ hP _] := dgpr_identities_smooth_extensions hS.
have hph (q : TX) : K0 q -> [/\ 0 <= (S q)^-1, 0 <= Rr q & (S q)^-1 * Rr q <= Mb].
  move=> hq; have hq' := hOm hq; have hSq := hSpos hq'.
  split; [by rewrite invr_ge0 ltW | exact: hR0 hq' |].
  by rewrite mulrC ler_pdivrMr //; exact: hRS hq.
have h := dgpr_relative_bilinear hND (dgpr_scalar_vector_bilinear hND) (phi3 := fun _ => Mb) hph
  (dgpr_heat_S_inverse_smooth hS) hP dgpr_regularity_S_inverse_ratio dgpr_regularity_Psi_ratio j.
have h1 (q : TX) : K0 q -> 0 <= (1 : R) /\ Mb <= Mb * 1.
  by move=> _; rewrite mulr1; split; [exact: ler01 | exact: lexx].
exact: (dgpr_relative_weaken (phi := fun _ => Mb) (psi := fun _ => 1) hMb h1 h).
Qed.

(** Source for [dgpr_regularity_kappa_ratio]: proof of lem:regularity,
    ||D^j kappa|| <= c (1 + |x|)^c on the strip:
    kappa = 2^(-1) R ((T - t)^(-1/2) S^(-1)), the derivatives of
    (T - t)^(-1/2) are bounded on the strip, and
    S^(-1) R <= (T - b)^(-1/2). *)
Lemma dgpr_regularity_kappa_ratio (j : nat) : WDA (C (fun _ => 1)) kappa j.
Proof.
have [_ _ hR _ _] := dgpr_identities_smooth_extensions hS.
have [_ hg] := dgpr_time_root_class n T.
have hI := dgpr_heat_S_inverse_smooth hS.
have hgI : norm_class_all_orders hNT hA OmT (fun q => irt q * (S q)^-1 : R^o).
  by move=> k; exact: (norm_class_scalar_product (hg k) (hI k)).
have hph1 (q : TX) : K0 q -> [/\ 0 <= (1 : R), 0 <= (S q)^-1 & 1 * (S q)^-1 <= (S q)^-1].
  move=> hq; have hSq := hSpos (hOm hq).
  by split; [exact: ler01 | rewrite invr_ge0 ltW | rewrite mul1r].
have h1 := dgpr_relative_bilinear hA (dgpr_scalar_mul_bilinear R) (phi1 := fun _ => 1)
  (phi2 := fun q => (S q)^-1) (phi3 := fun q => (S q)^-1) hph1 hg hI (dgpr_time_inverse_root_bound n a hbT)
  dgpr_regularity_S_inverse_ratio.
have hph2 (q : TX) : K0 q -> [/\ 0 <= Rr q, 0 <= (S q)^-1 & Rr q * (S q)^-1 <= Mb].
  move=> hq; have hq' := hOm hq; have hSq := hSpos hq'.
  split; [exact: hR0 hq' | by rewrite invr_ge0 ltW |].
  by rewrite ler_pdivrMr //; exact: hRS hq.
have h2 := dgpr_relative_bilinear hA (@dgpr_scalar_product_bilinear R (2^-1)) (phi1 := fun q => Rr q)
  (phi2 := fun q => (S q)^-1) (phi3 := fun _ => Mb) hph2 hR hgI dgpr_regularity_R_ratio h1 j.
have h3 (q : TX) : K0 q -> 0 <= (1 : R) /\ Mb <= Mb * 1.
  by move=> _; rewrite mulr1; split; [exact: ler01 | exact: lexx].
have h4 := dgpr_relative_weaken (phi := fun _ => Mb) (psi := fun _ => 1) hMb h3 h2.
have e : (fun q : TX => 2^-1 * (Rr q * (irt q * (S q)^-1)) : R^o) = kappa.
  by apply: funext => q; rewrite /dgpr_heat_kappa !invfM /=; ring.
by rewrite -e.
Qed.

(** Source for [dgpr_regularity_Q_one]: proof of lem:regularity,
    ||D^j q|| <= c (1 + |x|)^c on the strip, since q <= 1. *)
Lemma dgpr_regularity_Q_one (j : nat) : WDA (C (fun _ => 1)) Q j.
Proof.
have h1 (q : TX) : K0 q -> 0 <= (1 : R) /\ Q q <= 1 * 1.
  move=> hq; have hq' := hOm hq; have hSq := hSpos hq'; split; first exact: ler01.
  rewrite mul1r; change (rho q / S q <= 1); rewrite ler_pdivrMr // mul1r.
  exact: le_trans (hrhoU hq') (hUS hq').
exact: (dgpr_relative_weaken (phi := fun q => Q q) (psi := fun _ => 1) ler01 h1 (dgpr_regularity_Q_ratio j)).
Qed.

(** Source for [dgpr_regularity_log_ratio]: proof of lem:regularity,
    ||D^j log F|| <= c (1 + |x|)^c on the strip for F = S, rho, q:
    D log F = F^(-1) DF, the derivatives of F and F^(-1) have weights
    relative to F and F^(-1), and |log F| has polynomial growth. *)
Lemma dgpr_regularity_log_ratio (j : nat) :
  [/\ WDA (C (fun _ => 1)) (fun q => LOG (S q) : R^o) j,
      WDA (C (fun _ => 1)) (fun q => LOG (rho q) : R^o) j &
      WDA (C (fun _ => 1)) (fun q => LOG (Q q) : R^o) j].
Proof.
have [_ _ _ _ hr] := dgpr_identities_smooth_extensions hS.
have [_ _ _ hQ] := dgpr_regularity_smooth hS.
have [[c1 [hc1 h1]] [c2 [hc2 h2]] [c3 [hc3 h3]]] := dgpr_regularity_log_bounds.
have hQpos (q : TX) : OmT q -> 0 < Q q by move=> hq; exact: divr_gt0 (hrhopos hq) (hSpos hq).
split.
- exact: (dgpr_relative_logarithm hbT hSpos (dgpr_identities_smooth_S hS) dgpr_regularity_S_ratio hc1 h1 j).
- exact: (dgpr_relative_logarithm hbT hrhopos hr dgpr_regularity_rho_ratio hc2 h2 j).
- exact: (dgpr_relative_logarithm hbT hQpos hQ dgpr_regularity_Q_ratio hc3 h3 j).
Qed.
End Strip.

(** Source for [dgpr_regularity_S_gaussian]: blueprint lem:regularity,
    first assertion, for S: S has Gaussian decay before T. On each strip
    the derivatives of S are bounded by c (1 + |x|)^c S and
    S <= c0 exp(-|x|^2/c0). *)
Theorem dgpr_regularity_S_gaussian : dgpr_gaussian_decay_before hA T S.
Proof.
apply: (dgpr_relative_gaussian_decay (dgpr_identities_smooth_S hS)) => a b hbT.
have [c0 [hc0 hSg]] := dgpr_regularity_S_gaussian_bound a hbT.
exists (fun q => S q), c0; split => // j.
have h := dgpr_regularity_S_ratio a hbT j; exact h.
Qed.

(** Source for [dgpr_regularity_polynomial]: blueprint lem:regularity,
    second assertion, for B, eta, kappa and q: they have polynomial growth
    before T. *)
Theorem dgpr_regularity_polynomial :
  [/\ dgpr_polynomial_growth_before hNH T B, dgpr_polynomial_growth_before hND T eta,
      dgpr_polynomial_growth_before hA T kappa & dgpr_polynomial_growth_before hA T Q].
Proof.
have [hB heta hkappa hQ] := dgpr_regularity_smooth hS.
split.
- by apply: (dgpr_relative_polynomial_growth hB) => a b hbT j; exact (dgpr_regularity_B_ratio a hbT j).
- by apply: (dgpr_relative_polynomial_growth heta) => a b hbT j; exact (dgpr_regularity_eta_ratio a hbT j).
- by apply: (dgpr_relative_polynomial_growth hkappa) => a b hbT j; exact (dgpr_regularity_kappa_ratio a hbT j).
- by apply: (dgpr_relative_polynomial_growth hQ) => a b hbT j; exact (dgpr_regularity_Q_one a hbT j).
Qed.

(** Source for [dgpr_regularity_log_polynomial]: blueprint
    lem:regularity, second assertion, for log S, log rho and log q: they
    have polynomial growth before T. *)
Theorem dgpr_regularity_log_polynomial :
  [/\ dgpr_polynomial_growth_before hA T (fun q => LOG (S q) : R^o),
      dgpr_polynomial_growth_before hA T (fun q => LOG (rho q) : R^o) &
      dgpr_polynomial_growth_before hA T (fun q => LOG (Q q) : R^o)].
Proof.
have [hS1 hr1 hQ1] := dgpr_regularity_log_smooth hS.
split.
- apply: (dgpr_relative_polynomial_growth hS1) => a b hbT j.
  by have [h _ _] := dgpr_regularity_log_ratio a hbT j; exact h.
- apply: (dgpr_relative_polynomial_growth hr1) => a b hbT j.
  by have [_ h _] := dgpr_regularity_log_ratio a hbT j; exact h.
- apply: (dgpr_relative_polynomial_growth hQ1) => a b hbT j.
  by have [_ _ h] := dgpr_regularity_log_ratio a hbT j; exact h.
Qed.

(** Source for [dgpr_regularity_entropy_gaussian]: blueprint
    lem:regularity, consequence used in lem:DGPR31: rho log q has
    Gaussian decay before T, as the product of a function with polynomial
    growth before T and one with Gaussian decay before T (lem:classes). *)
Theorem dgpr_regularity_entropy_gaussian :
  dgpr_gaussian_decay_before hA T (fun p : TX => rho p * LOG (Q p)).
Proof.
have [_ _ hlQ] := dgpr_regularity_log_polynomial.
have [_ _ _ _ hr] := dgpr_regularity_gaussian_extensions hS.
exact: (dgpr_classes_product_gaussian_before hA (dgpr_scalar_mul_flip_bilinear R) hlQ hr).
Qed.

(** Source for [dgpr_regularity_B2_gaussian]: blueprint lem:regularity,
    consequence used in lem:DGPR31: rho |B|^2 has Gaussian decay before
    T, since |B|^2 = B . B has polynomial growth before T (lem:classes,
    with the inner product of Hom(R^n, Y) as bounded bilinear map) and rho
    has Gaussian decay before T. *)
Theorem dgpr_regularity_B2_gaussian :
  dgpr_gaussian_decay_before hA T (fun p : TX => rho p * hom_inner BX hCY heX (B p) (B p)).
Proof.
have [hB _ _ _] := dgpr_regularity_polynomial.
have hBB := dgpr_classes_product_polynomial_before hA (inner_product_norm_bounded_bilinear BH) hB hB.
have [_ _ _ _ hr] := dgpr_regularity_gaussian_extensions hS.
exact: (dgpr_classes_product_gaussian_before hA (dgpr_scalar_mul_flip_bilinear R) hBB hr).
Qed.
End Regularity.
