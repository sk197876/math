(** De Philippis, Gennaioli, Pigati and Rindler (2026), Lemma 3.2;
    blueprint dgpr_blueprint.tex, lem:DGPR32, under (S) alone:
      ∫_0^tau (I(rho_t) - (n - m) gamma / (2 (T - t))) dL^1 t
        <= (2n + C1 C) gamma (1 + log((1 + T^(1/2) delta)/gamma))
    for 0 <= tau < T, with C1 = (2n + 1)(32 Lambda / (3 lambda^2))^2 +
    32 / (3 lambda^2) and C = (16 n + 6) Lambda^2 + 16.

    The estimate eq:32:I at a fixed time (DgprLemma32Pointwise.v) needs
    two facts at time t, which lem:regularity (DgprRegularity.v) gives:
    D log rho_t has polynomial growth, and B_t is Lipschitzian on every
    ball {y : |y - x| <= 1} with a constant c (1 + |x|)^c. The sections
    at time t of maps of polynomial growth before T have polynomial
    growth (chain rule of Federer 3.1.11 for [x |-> (t,x)]); a map of
    polynomial growth is Lipschitzian on these balls by the bound on its
    differential and the convex-domain criterion of Federer 2.2.7. The
    integration over [0,tau] is DgprLemma32Final.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm InnerNormInequalities
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  LinearBasis HomInner HomInnerCoordinates ScalarInnerProduct ProductInner TensorUP Bilinear
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralBounds SummableRealFunctionUP SummableRealArithmetic RadonMeasureUP
  EuclideanLebesgueDimensions LebesgueScalarMeasure ScalarNormMetricCompleteness LocalUniquenessExample
  NormDifferentialUP NormDifferentialLinear NormDifferentialArithmetic NormOpenDomainLaws
  NormClassOneUP NormRegularity NormRegularityOperations NormClassHigherUP
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearOne NormOperatorNormUP
  NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherDifferentialFirst
  InnerConvex LipschitzUP LocalSlopeBound ConvexLocalLipschitz
  SmoothFunctionSpaceUP SmoothTestSpaces
  RealExponentialUP RealExponentialSealed RealExponentialLaws.
From DPGPR Require Import DgprDifferentialCalculus DgprGrowthClasses DgprIntegrationByPartsClasses
  DgprStanding DgprHeatObjects DgprIdentitiesSmooth DgprBackwardHeatDecay DgprHeatIntegral DgprLemma31Main
  DgprLemma31Final DgprRegularity DgprLemma31Field DgprLemma32Pointwise DgprLemma32Final.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Local Notation pw := dgpr_polynomial_weight.

Section SlicePolynomial.
Variable R : realType.
Variable n : nat.
Variable T : R.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BT := (product_inner_productP (scalar_inner_productP R)
  (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm BT).
Local Notation hNT := (inner_norm_real_norm BT).
Local Notation inj := (dgpr_space_injection R n).
Variables (Z : lmodType R) (NZ : Z -> R).
Hypothesis hNZ : is_real_norm NZ.
Local Notation lawss k := (@ContinuousMultilinear.laws R k X Z N NZ hN hNZ).

(** Source for [dgpr_slice_class_normed]: the section [x |-> f(t,x)] of
    a map of class k on Omega_T is of class k on R^n for t < T, by the
    chain rule of Federer 3.1.11, p. 220, for the affine map
    [x |-> (t,x)]. *)
Lemma dgpr_slice_class_normed (f : TX -> Z) (t : R) (k : nat) : t < T ->
  norm_class hNT hNZ (dgpr_before T) f k -> norm_class hN hNZ setT (fun x => f (t, x)) k.
Proof.
move=> ht hf.
have hLb : norm_bounded_linear N NT inj.
  by exists 1; split => // x; exact: dgpr_space_injection_bound.
have hL := norm_class_linear hN hNT k (fun x _ => norm_full_domain_interior N x) hLb.
have hC := norm_class_constant hN hNT (((t : R^o), (0 : X)) : TX) k
  (fun x _ => norm_full_domain_interior N x).
have hAff : norm_class hN hNT setT (fun x : X => (((t : R^o), x) : TX)) k.
  apply: (norm_class_domain_agreement _ (norm_class_add hL hC)) => x _.
  exact: dgpr_space_affine.
exact: (norm_class_compose_on (fun x _ => ht) hAff hf).
Qed.

(** Source for [dgpr_slice_polynomial]: if f has polynomial growth
    before T (def:classes), then the section [x |-> f(t,x)] has
    polynomial growth for t < T: its kth differential at x is the kth
    differential of f at (t,x) composed with the isometry [x |-> (0,x)]
    in every argument (Federer 3.1.11, chain rule), and the strip [t,t]
    is admissible. *)
Lemma dgpr_slice_polynomial (f : TX -> Z) (t : R) : t < T ->
  dgpr_polynomial_growth_before hNZ T f -> dgpr_polynomial_growth hNZ (fun x => f (t, x)).
Proof.
move=> ht [hcls hdec]; split; first by move=> k; exact: (dgpr_slice_class_normed ht (hcls k)).
move=> j; have [c [hc hb]] := hdec j t t ht.
exists c; split => // x z _ hz.
have [_ [D [hD _]]] := hcls j.
have [Pk [hPk hPkb]] := @dgpr_pullback_hom R X TX Z N NT NZ hN hNT hNZ
  inj 1 ler01 (@dgpr_space_injection_bound R n) j.
have hxp p : dgpr_before T (inj p + ((t : R^o), (0 : X))).
  by rewrite dgpr_space_affine.
have hx := hxp x.
have hpull := @dgpr_higher_differential_pullback R X TX Z N NT NZ hN hNT hNZ
  inj 1 ler01 (@dgpr_space_injection_bound R n) ((t : R^o), (0 : X)) (dgpr_before T)
  (@dgpr_before_open R n T) f j D Pk hPk hD x hx.
have eA : (fun p : X => dgpr_before T (inj p + ((t : R^o), (0 : X)))) = setT.
  by apply: funext => p; apply: propext; split => // _; exact: hxp.
have ef : (fun p : X => f (inj p + ((t : R^o), (0 : X)))) = (fun p => f (t, p)).
  by apply: funext => p; rewrite dgpr_space_affine.
rewrite eA ef dgpr_space_affine in hpull.
have ez := norm_higher_differential_unique hN hNZ (fun k => lawss k) hz hpull.
rewrite ez; apply: le_trans (hPkb _) _.
rewrite expr1n mul1r; apply: (hb (t, x)); first by rewrite /dgpr_time_strip /= lexx.
exact: hD.
Qed.
End SlicePolynomial.

Section LocalLipschitz.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation E := (@RealExponential.exponential R).
Local Notation L := (@RealExponential.logarithm R).
Local Notation h := (@RealExponential.laws R).
Variables (Z : lmodType R) (NZ : Z -> R).
Hypothesis hNZ : is_real_norm NZ.
Local Notation Zk k := (@ContinuousMultilinear.space R k X Z N NZ hN hNZ).
Local Notation lawsk k := (@ContinuousMultilinear.laws R k X Z N NZ hN hNZ).
Local Notation ZN k := (@ContinuousMultilinear.norm R k X Z N NZ hN hNZ).

(** Source for [dgpr_polynomial_weight_shift]: c (2 + r)^c <=
    c' (1 + r)^c' with c' = c exp(c log 2), since 2 + r <= 2 (1 + r);
    supporting def:classes. *)
Lemma dgpr_polynomial_weight_shift (c r : R) : 0 < c -> 0 <= r ->
  pw c (r + 1) <= pw (c * E (c * L 2)) r.
Proof.
move=> hc hr.
have hL2 : 0 <= L 2.
  rewrite -real_logarithm_one real_logarithm_order; lra.
have hE1 : 1 <= E (c * L 2).
  rewrite -[X in X <= _](real_exponential_zero h) real_exponential_order.
  exact: (mulr_ge0 (ltW hc) hL2).
have hcc : c <= c * E (c * L 2).
  by rewrite -{1}[c]mulr1; exact: (ler_wpM2l (ltW hc) hE1).
have hl := dgpr_log_one_plus_nonnegative hr.
rewrite !dgpr_polynomial_weightE //; last lra.
have hlog : L (1 + (r + 1)) <= L 2 + L (1 + r).
  rewrite -real_logarithm_product; [|lra|lra].
  rewrite real_logarithm_order; [lra|lra|].
  by apply: mulr_gt0; lra.
have h1 : E (c * L (1 + (r + 1))) <= E (c * L 2) * E (c * L (1 + r)).
  rewrite -(real_exponential_add h) real_exponential_order -mulrDr.
  exact: (ler_wpM2l (ltW hc) hlog).
have h2 : E (c * L (1 + r)) <= E (c * E (c * L 2) * L (1 + r)).
  rewrite real_exponential_order; exact: (ler_wpM2r hl hcc).
have hp1 := dgpr_exponential_positive (c * L 2).
have hp2 := dgpr_exponential_positive (c * L (1 + r)).
apply: le_trans (ler_wpM2l (ltW hc) h1) _.
rewrite mulrA; apply: ler_wpM2l => //.
by apply: mulr_ge0 => //; [exact: ltW | exact: ltW].
Qed.

(** Source for [dgpr_polynomial_local_lipschitz]: a map f of polynomial
    growth (def:classes) is Lipschitzian on every ball
    {y : |y - x| <= 1} with a constant at most c (1 + |x|)^c: on that
    convex set ||Df|| <= c1 (2 + |x|)^c1, which bounds every local
    quotient (Federer 3.1.1, p. 209), and the convex-domain criterion of
    Federer 2.2.7, p. 64, gives the Lipschitz bound. *)
Lemma dgpr_polynomial_local_lipschitz (f : X -> Z) : dgpr_polynomial_growth hNZ f ->
  exists c, 0 < c /\ forall x, exists Lx, 0 <= Lx /\ Lx <= pw c (N x) /\
    forall y z, N (y - x) <= 1 -> N (z - x) <= 1 -> NZ (f y - f z) <= Lx * N (y - z).
Proof.
move=> [hcls hgr].
have [c1 [hc1 hb1]] := hgr 1%N.
have [_ [D [hD _]]] := hcls 1%N.
have hdiff a : has_norm_differential N NZ setT f a
    (continuous_multilinear_one_operator (lawsk 1) (D a)).
  exact: ((norm_higher_differential_first hN hNZ (fun k => lawsk k) setT f a (D a)).1 (hD a I)).
have hop a v : NZ (continuous_multilinear_one_operator (lawsk 1) (D a) v) <= ZN 1 (D a) * N v.
  exact: (norm_operator_bound (continuous_multilinear_one_norm_laws (lawsk 1) (D a)) v).
have hDb a : ZN 1 (D a) <= pw c1 (N a) := hb1 a (D a) I (hD a I).
have hN0 := real_seminorm_nonnegative hN.1.
exists (c1 * E (c1 * L 2)); split.
  by apply: mulr_gt0 => //; exact: dgpr_exponential_positive.
move=> x; exists (pw c1 (N x + 1)).
have hM0 : 0 <= pw c1 (N x + 1).
  exact: (dgpr_polynomial_weight_nonnegative _ (ltW hc1)).
split => //; split; first exact: (dgpr_polynomial_weight_shift hc1 (hN0 x)).
pose Bx : set (real_norm_metric_space hN) := fun y : X => N (y - x) <= 1.
have hconv : is_inner_convex Bx.
  move=> y z hy hz s hs0 hs1; rewrite /Bx /=.
  have -> : (1 - s) *: y + s *: z - x = (1 - s) *: (y - x) + s *: (z - x).
    by rewrite !scalerBr addrACA -opprD -scalerDl subrK scale1r.
  apply: le_trans (real_seminorm_triangle hN.1 _ _) _.
  rewrite !(real_seminorm_scale hN.1) !ger0_norm //; last lra.
  have hy' : N (y - x) <= 1 := hy.
  have hz' : N (z - x) <= 1 := hz.
  nra.
have hloc : is_metric_local_slope_bound (U := real_norm_metric_space hNZ) Bx f (pw c1 (N x + 1)).
  move=> a ha L' hL'.
  have [_ _ hrem] := hdiff a.
  have he : 0 < L' - pw c1 (N x + 1) by rewrite subr_gt0.
  have [d [hd hr]] := hrem (L' - pw c1 (N x + 1)) he.
  exists d; split => // y _ hdist.
  rewrite !real_norm_metric_distanceE in hdist *.
  have hya : N (y - a) < d by rewrite (real_seminorm_subtract hN.1).
  have hra := hr (y - a) I hya.
  rewrite [a + (y - a)]addrC subrK in hra.
  have hNa : N a <= N x + 1.
    have ha' : N (a - x) <= 1 := ha.
    have ht := real_seminorm_triangle hN.1 (a - x) x.
    rewrite subrK in ht; lra.
  have hDa : ZN 1 (D a) <= pw c1 (N x + 1).
    exact: (le_trans (hDb a) (dgpr_polynomial_weight_monotone (ltW hc1) (hN0 a) hNa)).
  set Lh := continuous_multilinear_one_operator (lawsk 1) (D a) (y - a).
  have ht := real_seminorm_triangle hNZ.1 (f y - f a - Lh) Lh.
  rewrite subrK in ht.
  have hLh : NZ Lh <= pw c1 (N x + 1) * N (y - a).
    apply: le_trans (hop a (y - a)) _; apply: ler_wpM2r => //; exact: hN0.
  rewrite (real_seminorm_subtract hNZ.1) (real_seminorm_subtract hN.1 a y).
  have hNya := hN0 (y - a).
  nra.
have [_ hlip] := convex_local_slope_bound_global hconv hM0 hloc.
move=> y z hy hz.
have hh := hlip y z hy hz.
by rewrite !real_norm_metric_distanceE in hh.
Qed.
End LocalLipschitz.

Section Lemma32Theorem.
Variable R : realType.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
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
Local Notation LL := (@euclidean_lebesgue_measure R n).
Local Notation L1 := (@lebesgue_scalar_measure R).
Local Notation B := (dgpr_heat_B hS).
Local Notation rho := (dgpr_heat_rho hS).
Local Notation LOG := (@RealExponential.logarithm R).

(** Source for [dgpr_lemma32_log_rho_growth]: lem:regularity: for t < T,
    D log rho_t has polynomial growth, the hypothesis of lem:ibp for
    rho_t; the section at time t of [(t,x) |-> log rho(t,x)]. *)
Lemma dgpr_lemma32_log_rho_growth (t : R) : t < T ->
  dgpr_log_derivative_polynomial_growth (fun x => rho (t, x)).
Proof.
move=> ht.
have [_ hlr _] := dgpr_regularity_log_polynomial hS.
have [hcls hgr] := dgpr_slice_polynomial ht hlr.
by split => // j _; exact: hgr.
Qed.

(** Source for [dgpr_lemma32_B_lipschitz]: lem:regularity: for t < T,
    B_t is Lipschitzian on every ball {y : |y - x| <= 1} with a constant
    at most c (1 + |x|)^c; the statement "B_t is locally Lipschitzian of
    polynomial growth" of the proof of lem:DGPR32. *)
Lemma dgpr_lemma32_B_lipschitz (t : R) : t < T ->
  exists c, 0 < c /\ forall x, exists Lx, 0 <= Lx /\ Lx <= pw c (N x) /\
    forall y z, N (y - x) <= 1 -> N (z - x) <= 1 -> NH (B (t, y) - B (t, z)) <= Lx * N (y - z).
Proof.
move=> ht.
have [hB _ _ _] := dgpr_regularity_polynomial hS.
exact: (dgpr_polynomial_local_lipschitz (dgpr_slice_polynomial ht hB)).
Qed.

(** Source for [dgpr_lemma_3_2]: DPGPR 2026, Lemma 3.2, and blueprint
    lem:DGPR32: eq:32:I at each time ([dgpr_lemma32_fixed_time], with
    [dgpr_lemma32_log_rho_growth] and [dgpr_lemma32_B_lipschitz]),
    integrated over [0,tau] ([dgpr_lemma_3_2_conditional]), with the
    Gaussian decay before T of rho log q and rho |B|^2 from
    lem:regularity. *)
Theorem dgpr_lemma_3_2 (DB : TX -> X -> Hom X Y) (tau : R) :
  (forall t x, t < T -> dgpr_differential_values NH (fun z => B (t, z)) x (DB (t, x))) ->
  0 <= tau < T ->
  (measure_subset_upper_integral L1 `[0%R, tau]
     (partial_function_total (fun t : R =>
        dgpr_fisher_information hS t - ((n - m)%N%:R * gamma / (2 * (T - t)))%:E))
   <= ((2 * n%:R + dgpr_lemma32_C1 n lam Lam * ((16 * n%:R + 6) * Lam ^+ 2 + 16)) * gamma *
        (1 + LOG ((1 + Num.sqrt T * delta) / gamma)))%:E)%E.
Proof.
move=> hDB htau.
have hI32 t : 0 <= t < T ->
    (dgpr_fisher_information hS t <=
      ((n - m)%N%:R * gamma / (2 * (T - t)) + n%:R / 2 * dgpr_lemma31_m delta T gamma t)%:E +
      (dgpr_lemma32_C1 n lam Lam)%:E * measure_upper_integral LL
        (real_total_integrand (fun x => dgpr_lemma31_integrand hS DB (t, x))))%E.
  move=> /andP [_ htT].
  exact (dgpr_lemma32_fixed_time htT (fun x => hDB t x htT) (dgpr_lemma32_log_rho_growth htT)
    (dgpr_lemma32_B_lipschitz htT)).
exact (dgpr_lemma_3_2_conditional hDB (dgpr_regularity_entropy_gaussian hS)
  (dgpr_regularity_B2_gaussian hS) (ltW (dgpr_lemma32_C1_gt0 hS)) hI32 htau).
Qed.
End Lemma32Theorem.
