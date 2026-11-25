(** De Philippis, Gennaioli, Pigati and Rindler (2026), proof of
    Lemma 3.2; blueprint dgpr_blueprint.tex, proof of lem:DGPR32, the
    estimate (eq:32:I) at a fixed time t < T:

      I(rho_t) <= (n - m) gamma / (2 (T - t)) + (n/2) m(t)
                  + C_1 ∫ rho_t (|D B_t|^2 + |B_t(grad log rho_t)|^2) dL^n,

    with C_1 = (2n + 1)(32 Lambda/(3 lambda^2))^2 + 32/(3 lambda^2) and the
    upper integral of Federer 2.4.2 on the right. With
    Q(x) = chi^(B(t,x)* o B(t,x)) (DgprLemma32Spectral.v) and
    e_j(x) = Q(x)(eps_j), the proof follows the blueprint: lem:semiconvex
    gives D^2 log rho_t(x)(v,v) >= -(2(T-t))^(-1)|v|^2, lem:trace gives
    (eq:32:split), lem:identities(sv) and lem:sv(eigen) give |Q(x)|^2 >= m
    where U >= (T-t)^(1/2) R, and lem:ibp is applied to the constant fields
    eps_j (which yields I(rho_t) = -∫ rho_t Delta log rho_t, in place of
    lem:classes(cl:div)) and to the fields e_j. The differential of Q is
    estimated by (eq:32:DQ) at the points where all e_j are
    differentiable.

    Two regularity facts at time t enter as hypotheses of the section:
    [hrho_logpoly], D log rho_t has polynomial growth (def:classes, as
    required by lem:ibp), and [hB_lip], B_t is locally Lipschitzian with a
    local Lipschitz constant of polynomial growth; the latter gives, with
    lem:spectral, that the e_j are locally Lipschitzian maps of polynomial
    growth. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm InnerNormInequalities
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  LinearBasis HomInner HomInnerCoordinates OrthonormalFamilies EuclideanStiefelInnerSplitting
  EuclideanCoordinateMetric CoordinateProjection SymmetricEndomorphisms
  ScalarInnerProduct ProductInner TensorUP Bilinear CompleteMetricUP PartialFunctionUP PartialFunctionBasic
  PartialExtendedOrderLoci OperatorNorm HomNormBound
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralComparison MeasureIntegralUniqueness MeasureUpperIntegralMonotone
  SummableRealFunctionUP SummableRealArithmetic RadonMeasureUP EuclideanLebesgueDimensions
  ScalarNormMetricCompleteness LocalUniquenessExample
  NormDifferentialUP NormDifferentialDirectional NormDifferentialLinear NormClassOneUP NormRegularity
  SmoothFunctionSpaceUP SmoothTestSpaces
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearOne
  MultilinearSuccessorArguments NormHigherDifferentialUP
  RealExponentialUP RealExponentialSealed.
From DPGPR Require Import DgprOrthonormalCoordinates DgprHomNorms DgprHeatKernel DgprHeatExtension
  DgprDifferentialCalculus DgprHeatJets DgprBackwardHeat DgprStanding DgprHeatObjects DgprIdentities
  DgprFunctionals DgprHeatJetCalculus DgprHeatCalculus DgprIdentitiesDivergence DgprIdentitiesSmooth
  DgprMeasureComparison DgprLemma31 DgprGrowthClasses DgprIntegrationByPartsClasses DgprHeatIntegral
  DgprHeatSemiconvex DgprLemma31Main DgprSingularValue DgprTraceComparison DgprDivergenceIntegral
  DgprIntegrationByPartsGeneral DgprLemma32Spectral DgprLemma32Calculus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [dgpr_lemma32_K]: proof of lem:DGPR32, eq:32:DQ, the
    constant 2 Lambda Lip(chi) = 32 Lambda/(3 lambda^2). *)
Definition dgpr_lemma32_K (R : realType) (lam Lam : R) : R := 2 * Lam * dgpr_chi_constant lam.

(** Source for [dgpr_lemma32_C1]: proof of lem:DGPR32, eq:32:I,
    C_1 = (2n + 1)(32 Lambda/(3 lambda^2))^2 + 32/(3 lambda^2). *)
Definition dgpr_lemma32_C1 (R : realType) (n : nat) (lam Lam : R) : R :=
  (2 * n%:R + 1) * dgpr_lemma32_K lam Lam ^+ 2 + 2 * dgpr_chi_constant lam.

Section Lemma32.
Variable R : realType.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Local Notation eps := (@coordinate_basis R n).
Local Notation orth := (@euclidean_coordinate_orthonormal_family R n).
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
Local Notation BH := (hom_inner_productP BX hCY heX).
Local Notation NH := (hom_norm BX hCY heX).
Local Notation hNH := (inner_norm_real_norm BH).
Local Notation BXX := (hom_inner_productP BX BX heX).
Local Notation HXX := (hom_norm BX BX heX).
Local Notation hHXX := (inner_norm_real_norm BXX).
Local Notation hZ1 := (@scalar_norm_metric_complete R).
Variable K : set (real_norm_metric_space hNH).
Variables lam Lam : R.
Variable mu : set X -> \bar R.
Variable r0 : R.
Variable Xf : X -> Hom X Y.
Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space (inner_norm_real_norm BX) (inner_norm_real_norm hCY) setT ev.
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
Local Notation hlam := (dgpr_standing_lambda hS).
Local Notation hLam := (dgpr_standing_Lambda hS).
Local Notation LL := (@euclidean_lebesgue_measure R n).
Local Notation hLL := (euclidean_lebesgue_is_measure R n).
Local Notation B := (dgpr_heat_B hS).
Local Notation U := (dgpr_heat_U hS).
Local Notation Rr := (dgpr_heat_R hS).
Local Notation rho := (dgpr_heat_rho hS).
Local Notation LOG := (@RealExponential.logarithm R).
Local Notation pw := dgpr_polynomial_weight.
Local Notation chic := (dgpr_chi_constant lam).
Local Notation KQ := (dgpr_lemma32_K lam Lam).
Local Notation C1 := (dgpr_lemma32_C1 n lam Lam).
Local Notation emin := (dgpr_lemma31_min hS).
Local Notation ZR k := (@ContinuousMultilinear.space R k X R^o N A1 hN hA).
Local Notation evR k := (@ContinuousMultilinear.evaluation R k X R^o N A1 hN hA).
Local Notation args2 w v := (multilinear_successor_arguments [ffun _ : 'I_1 => w] v).
Local Notation grad := (dgpr_heat_grad_log_rho hS).

Variable t : R.
Hypothesis ht : t < T.
Variable DB : TX -> X -> Hom X Y.
Hypothesis hDB : forall x, dgpr_differential_values NH (fun z => B (t, z)) x (DB (t, x)).
Hypothesis hrho_logpoly : dgpr_log_derivative_polynomial_growth (fun x => rho (t, x)).
Hypothesis hB_lip : exists c, 0 < c /\ forall x, exists L, 0 <= L /\ L <= pw c (N x) /\
  forall y z, N (y - x) <= 1 -> N (z - x) <= 1 -> NH (B (t, y) - B (t, z)) <= L * N (y - z).

(** Source for [dgpr_lemma32_Q]: proof of lem:DGPR32,
    Q(x) = chi^(B(t,x)* o B(t,x)). *)
Definition dgpr_lemma32_Q (x : X) : Hom X X := dgpr_Q BX hCY heX lam (B (t, x)).
Local Notation Qx := dgpr_lemma32_Q.

(** Source for [dgpr_lemma32_e]: proof of lem:DGPR32,
    e_j = [x |-> Q(x)(eps_j)]. *)
Definition dgpr_lemma32_e (j : 'I_n) (x : X) : X := Qx x (eps j).
Local Notation ej := dgpr_lemma32_e.

(** Source for [dgpr_lemma32_Dh]: D log rho_t(x), the differential of
    Federer 3.1.1 (it exists by [hrho_logpoly]). *)
Definition dgpr_lemma32_Dh (x : X) : Hom X R^o :=
  xget 0 [set L | has_norm_differential N A1 setT (fun y => LOG (rho (t, y))) x L].
Local Notation Dh := dgpr_lemma32_Dh.

(** Source for [dgpr_lemma32_D2h]: D^2 log rho_t(x), Federer 3.1.11. *)
Definition dgpr_lemma32_D2h (x : X) : ZR 2 :=
  xget 0 [set z | dgpr_higher_differential hN hA setT (fun y => LOG (rho (t, y))) 2 x z].
Local Notation D2h := dgpr_lemma32_D2h.

(** Source for [dgpr_lemma32_hessian]: h(x)(v,v) = D^2 log rho_t(x)(v,v),
    proof of lem:DGPR32. *)
Definition dgpr_lemma32_hessian (x v : X) : R := evR 2 [ffun _ : 'I_2 => v] (D2h x).
Local Notation hess := dgpr_lemma32_hessian.

(** Source for [dgpr_lemma32_De]: a differential of e_j at x, where one
    exists (Federer 3.1.1); 0 elsewhere. *)
Definition dgpr_lemma32_De (j : 'I_n) (x : X) : Hom X X :=
  xget 0 [set D | has_norm_differential N N setT (ej j) x D].
Local Notation De := dgpr_lemma32_De.

(** Source for [dgpr_lemma32_pos]: lem:identities(bounds), rho > 0. *)
Lemma dgpr_lemma32_pos (x : X) : 0 < rho (t, x).
Proof. by have [[h _] _ _ _ _] := dgpr_identities_bounds_full hS x ht. Qed.

(** Source for [dgpr_lemma32_B_norm]: lem:identities(bounds),
    |B(t,x)| <= Lambda. *)
Lemma dgpr_lemma32_B_norm (x : X) : NH (B (t, x)) <= Lam.
Proof. by have [_ _ _ [_ h] _] := dgpr_identities_bounds_full hS x ht. Qed.

(** Source for [dgpr_lemma32_K_ge0]: 32 Lambda/(3 lambda^2) >= 0. *)
Lemma dgpr_lemma32_K_ge0 : 0 <= KQ.
Proof.
rewrite /dgpr_lemma32_K; apply: mulr_ge0; first by apply: mulr_ge0 => //; exact: ltW hLam.
exact: ltW (dgpr_chi_constant_gt0 hlam).
Qed.

(** Source for [dgpr_lemma32_C1_gt0]: C_1 > 0. *)
Lemma dgpr_lemma32_C1_gt0 : 0 < C1.
Proof.
have hc := dgpr_chi_constant_gt0 hlam.
have hn : 0 <= (2 * n%:R + 1) * KQ ^+ 2.
  by apply: mulr_ge0; [rewrite addr_ge0 // mulr_ge0 | exact: sqr_ge0].
rewrite /dgpr_lemma32_C1; lra.
Qed.

(** Source for [dgpr_lemma32_Q_difference]: lem:spectral with
    |B| <= Lambda: |Q(y) - Q(z)| <= 2 Lambda Lip(chi) |B(t,y) - B(t,z)|. *)
Lemma dgpr_lemma32_Q_difference (y z : X) : HXX (Qx y - Qx z) <= KQ * NH (B (t, y) - B (t, z)).
Proof.
apply: le_trans (dgpr_Q_lipschitz BX hCY heX heY hlam (B (t, y)) (B (t, z))) _.
have ha := dgpr_lemma32_B_norm y; have hb := dgpr_lemma32_B_norm z.
have hh : 0 <= NH (B (t, y) - B (t, z)) := inner_norm_nonnegative _ _.
have hc := ltW (dgpr_chi_constant_gt0 hlam).
have h1 : (NH (B (t, y)) + NH (B (t, z))) * NH (B (t, y) - B (t, z)) <=
    (2 * Lam) * NH (B (t, y) - B (t, z)) by apply: ler_wpM2r => //; lra.
apply: le_trans (ler_wpM2l hc h1) _.
have e : chic * (2 * Lam * NH (B (t, y) - B (t, z))) = KQ * NH (B (t, y) - B (t, z)).
  by rewrite /dgpr_lemma32_K; ring.
by rewrite e.
Qed.

(** Source for [dgpr_lemma32_e_le1]: ||Q(x)|| <= 1, hence |e_j(x)| <= 1. *)
Lemma dgpr_lemma32_e_le1 (j : 'I_n) (x : X) : N (ej j x) <= 1.
Proof.
have h := linear_operator_norm_bound BX BX heX (hom_as_linear (Qx x)) (eps j).
rewrite hom_as_linearE euclidean_coordinate_unit_norm mulr1 in h.
exact: le_trans h (dgpr_Q_operator_norm BX hCY heX hlam (B (t, x))).
Qed.

(** Source for [dgpr_lemma32_e_difference]:
    |e_j(y) - e_j(z)| <= |Q(y) - Q(z)| <= 2 Lambda Lip(chi) |B(t,y) - B(t,z)|. *)
Lemma dgpr_lemma32_e_difference (j : 'I_n) (y z : X) :
  N (ej j y - ej j z) <= KQ * NH (B (t, y) - B (t, z)).
Proof.
have -> : ej j y - ej j z = (Qx y - Qx z) (eps j) by rewrite dgpr_hom_subE.
apply: le_trans (hom_norm_vector_bound BX BX heX (Qx y - Qx z) (eps j)) _.
by rewrite euclidean_coordinate_unit_norm mulr1; exact: dgpr_lemma32_Q_difference.
Qed.

(** Source for [dgpr_lemma32_e_growth]: proof of lem:DGPR32, the maps
    e_j are locally Lipschitzian maps of polynomial growth
    (def:classes), by [hB_lip], lem:spectral and |e_j| <= 1. *)
Lemma dgpr_lemma32_e_growth (j : 'I_n) : dgpr_lipschitz_polynomial_growth (ej j).
Proof.
have [c [hc hL]] := hB_lip.
have hK := dgpr_lemma32_K_ge0.
have hKc : 0 < KQ * c + c by have := mulr_ge0 hK (ltW hc); lra.
exists (1 + (KQ * c + c)); split; first exact: addr_gt0 ltr01 hKc.
move=> x; have [L [hL0 [hLw hLip]]] := hL x.
have hNx := inner_norm_nonnegative BX x.
exists (KQ * L); split; first exact: mulr_ge0.
split.
- apply: le_trans (_ : 1 + KQ * pw c (N x) <= _).
    by apply: lerD; [exact: dgpr_lemma32_e_le1 | exact: ler_wpM2l].
  apply: le_trans (_ : pw 1 (N x) + pw (KQ * c + c) (N x) <= _).
    apply: lerD; first exact: (dgpr_polynomial_weight_one ler01 hNx).
    exact: (dgpr_weight_scale hK hc hNx).
  exact: (dgpr_polynomial_weight_sum ltr01 hKc hNx).
- move=> y z hy hz; apply: le_trans (dgpr_lemma32_e_difference j y z) _.
  have h := ler_wpM2l hK (hLip y z hy hz); rewrite mulrA in h; exact: h.
Qed.

(** Source for [dgpr_lemma32_constant_growth]: the constant map eps_j is
    a locally Lipschitzian map of polynomial growth (def:classes). *)
Lemma dgpr_lemma32_constant_growth (j : 'I_n) : dgpr_lipschitz_polynomial_growth (fun _ : X => eps j).
Proof.
exists 1; split => // x; exists 0; split => //; split.
  rewrite addr0 euclidean_coordinate_unit_norm.
  exact: (dgpr_polynomial_weight_one ler01 (inner_norm_nonnegative _ _)).
by move=> y z _ _; rewrite subrr inner_norm0 mul0r.
Qed.

(** Source for [dgpr_lemma32_gauss]: lem:regularity, rho_t has Gaussian
    decay (def:classes). *)
Lemma dgpr_lemma32_gauss : dgpr_gaussian_decay hA (fun x => rho (t, x)).
Proof. by have [_ _ _ _ hr] := dgpr_regularity_gaussian_extensions hS; exact: dgpr_slice_gaussian ht hr. Qed.

(** Source for [dgpr_lemma32_DhP]: D log rho_t(x) exists, Federer 3.1.1. *)
Lemma dgpr_lemma32_DhP (x : X) : has_norm_differential N A1 setT (fun y => LOG (rho (t, y))) x (Dh x).
Proof.
apply: xgetPex.
have [D hD] := (norm_class_firstP hN hA setT (fun y => LOG (rho (t, y)))).1 (hrho_logpoly.1 1%N).
by exists (D x); exact: (norm_class_one_differential hD (Logic.I : setT x)).
Qed.

(** Source for [dgpr_lemma32_D2hP]: D^2 log rho_t(x) exists, Federer
    3.1.11. *)
Lemma dgpr_lemma32_D2hP (x : X) :
  dgpr_higher_differential hN hA setT (fun y => LOG (rho (t, y))) 2 x (D2h x).
Proof.
apply: xgetPex.
have [_ [D [hD _]]] := hrho_logpoly.1 2%N.
by exists (D x); exact: hD x Logic.I.
Qed.

(** Source for [dgpr_lemma32_fields]: lem:ibp, proof, first order data
    of log rho_t: D rho_t = rho_t D log rho_t, and
    [y |-> D log rho_t(y)(w)] has the differential [v |-> H(x)(v)(w)] with
    H(x)(v)(w) = D^2 log rho_t(x)(w, v) (Federer 3.1.11). *)
Lemma dgpr_lemma32_fields : exists H2 : X -> Hom X (Hom X R^o),
  (forall x, dgpr_differential_values A1 (fun y => rho (t, y)) x (fun v => rho (t, x) * Dh x v)) /\
  (forall x w, dgpr_differential_values A1 (fun y => Dh y w) x (fun v => H2 x v w)) /\
  (forall x v w, H2 x v w = evR 2 (args2 w v) (D2h x)).
Proof.
have [c [H2 [_ [_ [h1 [h2 [h3 _]]]]]]] := dgpr_log_density_fields dgpr_lemma32_gauss
  dgpr_lemma32_pos hrho_logpoly dgpr_lemma32_DhP dgpr_lemma32_D2hP.
by exists H2.
Qed.

(** Source for [dgpr_lemma32_hessianE]: the pair (v, v) as two arguments,
    Federer 3.1.11. *)
Lemma dgpr_lemma32_hessianE (x v : X) : hess x v = evR 2 (args2 v v) (D2h x).
Proof.
rewrite /dgpr_lemma32_hessian dgpr_two_arguments; congr (evR 2 _ (D2h x)).
by apply/ffunP => i; rewrite !ffunE if_same.
Qed.

(** Source for [dgpr_differential_congr]: Federer 3.1.1: the
    differential depends only on the function. *)
Lemma dgpr_differential_congr (f g : X -> R^o) (a : X) (L : Hom X R^o) :
  (forall y, f y = g y) -> has_norm_differential N A1 setT g a L ->
  has_norm_differential N A1 setT f a L.
Proof. by move=> hfg; have -> : f = g by apply: funext. Qed.

(** Source for [dgpr_lemma32_semiconvex]: lem:semiconvex with
    s = T - t, nu = mu0: h(x)(v,v) >= -(2(T-t))^(-1) |v|^2. *)
Lemma dgpr_lemma32_semiconvex (x v : X) : - ((2 * (T - t))^-1 * N v ^+ 2) <= hess x v.
Proof.
have [H2 [_ [hH2 hH2v]]] := dgpr_lemma32_fields.
have hs : 0 < T - t by rewrite subr_gt0.
have hsc y := dgpr_semiconvex hmu0 hOmu0 hMmu0 (dgpr_standing_mu0_support hS)
  (dgpr_standing_gamma hS) y v hs.
have [_ [_ [H [hH hHv]]]] := hsc x.
have hDv : has_norm_differential N A1 setT (fun y => Dh y v) x H.
  apply: (dgpr_differential_congr _ hH) => y.
  have [[G [hG hGv]] _] := hsc y.
  by rewrite (norm_differential_unique hN hA (dgpr_lemma32_DhP y) hG) hGv.
have [L [hL hLv]] := hH2 x v.
rewrite dgpr_lemma32_hessianE -hH2v -hLv (norm_differential_unique hN hA hL hDv).
exact: hHv.
Qed.

(** Source for [dgpr_lemma32_split]: proof of lem:DGPR32, eq:32:split,
    by lem:trace applied to g = h(x) + (2(T-t))^(-1) [(v,w) |-> v . w]
    and Q(x):
    -Delta log rho_t(x) <= (n - |Q(x)|^2)/(2(T-t)) - sum_j h(x)(e_j(x),e_j(x)). *)
Lemma dgpr_lemma32_split (x : X) :
  \sum_j - hess x (eps j) <=
    (2 * (T - t))^-1 * (n%:R - HXX (Qx x) ^+ 2) - \sum_j hess x (ej j x).
Proof.
have [H2 [_ [_ hH2v]]] := dgpr_lemma32_fields.
have eh v : hess x v = H2 x v v by rewrite dgpr_lemma32_hessianE hH2v.
pose c := (2 * (T - t))^-1.
pose g (v w : X) : R := H2 x v w + c * euclidean_inner_product v w.
have sc (p q : R) : p *: (q : R^o) = p * q by [].
have hg : @bilinear R X X R^o g.
  split => [w|v] a y z; rewrite /g.
  - rewrite linearP hom_addE hom_scaleE ((inner_bilinear BX).1 w a y z) /= !sc; ring.
  - rewrite linearP ((inner_bilinear BX).2 v a y z) /= !sc; ring.
have hg0 v : 0 <= g v v.
  have h := dgpr_lemma32_semiconvex x v; rewrite eh (inner_norm_sqr BX) in h.
  rewrite /g /c; lra.
have htr := dgpr_trace_comparison hg hg0 (dgpr_Q_symmetric BX hCY heX lam (B (t, x)))
  (dgpr_Q_operator_norm BX hCY heX hlam (B (t, x))) heX orth.
rewrite /g !big_split -!mulr_sumr /= in htr.
have eQ : \sum_j euclidean_inner_product (Qx x (eps j)) (Qx x (eps j)) = HXX (Qx x) ^+ 2.
  by rewrite (dgpr_hom_norm_sqr BX BX heX (Qx x) heX orth).
have eI : \sum_j euclidean_inner_product (eps j) (eps j) = n%:R.
  rewrite (eq_bigr (fun _ => 1)) => [|j _]; first by rewrite sumr_const card_ord.
  exact: (orthonormal_diagonal orth).
rewrite eQ eI in htr.
have e1 : \sum_j - hess x (eps j) = - \sum_j H2 x (eps j) (eps j).
  by rewrite -sumrN; apply: eq_bigr => j _; rewrite eh.
have e2 : \sum_j hess x (ej j x) = \sum_j H2 x (Qx x (eps j)) (Qx x (eps j)).
  by apply: eq_bigr => j _; rewrite eh.
rewrite e1 e2 -/c; lra.
Qed.

(** Source for [dgpr_lemma32_trace_term]: proof of lem:DGPR32,
    eq:32:trace in pointwise form: on G = {U >= (T-t)^(1/2) R} one has
    |Q|^2 >= m (lem:identities(sv), lem:sv(eigen)); off G,
    rho <= U < (T-t)^(1/2) R, so that rho/(T-t) <= R/(T-t)^(1/2). Hence
    rho (n - |Q|^2)/(2(T-t)) <= (n - m) rho/(2(T-t)) + (n/2) min{rho/(T-t), R/(T-t)^(1/2)}. *)
Lemma dgpr_lemma32_trace_term (x : X) :
  rho (t, x) * ((2 * (T - t))^-1 * (n%:R - HXX (Qx x) ^+ 2)) <=
    (2 * (T - t))^-1 * ((n%:R - m%:R) * rho (t, x)) + n%:R / 2 * emin (t, x).
Proof.
have hs : 0 < T - t by rewrite subr_gt0.
have [[hr0 hrU] _ _ _ _] := dgpr_identities_bounds_full hS x ht.
have hR0 := dgpr_identities_R_ge0 hS x ht.
have hmn : m%:R <= n%:R :> R by rewrite ler_nat; case/andP: hm.
have hq : 0 < Num.sqrt (T - t) by rewrite sqrtr_gt0.
have hqq : Num.sqrt (T - t) * Num.sqrt (T - t) = T - t by rewrite -expr2 sqr_sqrtr // ltW.
have hc : 0 < (2 * (T - t))^-1 by rewrite invr_gt0 mulr_gt0.
have hn0 : 0 <= n%:R / 2 :> R by rewrite divr_ge0.
have ha1 : 0 <= (T - t)^-1 * rho (t, x) by rewrite mulr_ge0 // ?invr_ge0 ltW.
have ha2 : 0 <= (Num.sqrt (T - t))^-1 * Rr (t, x) by rewrite mulr_ge0 // invr_ge0 ltW.
have hmin0 : 0 <= emin (t, x) by rewrite /dgpr_lemma31_min /= le_min ha1 ha2.
have hrc : 0 <= rho (t, x) * (2 * (T - t))^-1 by rewrite mulr_ge0 // ltW.
have e1 : rho (t, x) * ((2 * (T - t))^-1 * (n%:R - HXX (Qx x) ^+ 2)) =
    rho (t, x) * (2 * (T - t))^-1 * n%:R - rho (t, x) * (2 * (T - t))^-1 * HXX (Qx x) ^+ 2.
  by ring.
have e2 : (2 * (T - t))^-1 * ((n%:R - m%:R) * rho (t, x)) =
    rho (t, x) * (2 * (T - t))^-1 * n%:R - rho (t, x) * (2 * (T - t))^-1 * m%:R by ring.
rewrite e1 e2.
case: (lerP (Num.sqrt (T - t) * Rr (t, x)) (U (t, x))) => hUR.
- have hsv := dgpr_identities_sv ht hUR.
  have hQm : m%:R <= HXX (Qx x) ^+ 2 := dgpr_Q_hom_norm_lower hlam hsv.
  have h1 := ler_wpM2l hrc hQm.
  have h2 := mulr_ge0 hn0 hmin0.
  lra.
- have hrR : rho (t, x) <= Num.sqrt (T - t) * Rr (t, x) by apply: le_trans hrU (ltW hUR).
  have ha12 : (T - t)^-1 * rho (t, x) <= (Num.sqrt (T - t))^-1 * Rr (t, x).
    have ei : (T - t)^-1 = (Num.sqrt (T - t))^-1 * (Num.sqrt (T - t))^-1 by rewrite -invfM hqq.
    rewrite ei -mulrA; apply: ler_wpM2l; first by rewrite invr_ge0 ltW.
    by rewrite ler_pdivrMl.
  have hmin1 : (T - t)^-1 * rho (t, x) <= emin (t, x).
    by rewrite /dgpr_lemma31_min /= le_min lexx ha12.
  have e3 : n%:R / 2 * ((T - t)^-1 * rho (t, x)) = rho (t, x) * (2 * (T - t))^-1 * n%:R.
    by field; rewrite gt_eqF.
  have h3 := ler_wpM2l hn0 hmin1.
  rewrite e3 in h3.
  have h4 := mulr_ge0 hrc (sqr_ge0 (HXX (Qx x))).
  have h5 := ler_wpM2l hrc hmn.
  lra.
Qed.

(** Source for [dgpr_lemma32_Dh_rho]: D rho_t(x)(v) = rho_t(x) D log rho_t(x)(v)
    (Federer 3.1.1, uniqueness of the differential). *)
Lemma dgpr_lemma32_Dh_rho (x v : X) : rho (t, x) * Dh x v = dgpr_heat_rho_first hS t x v.
Proof.
have [H2 [hDr _]] := dgpr_lemma32_fields.
have [L1 [h1 v1]] := hDr x.
have [L2 [h2 v2]] := dgpr_lemma31_rho_first hS x ht.
by rewrite -v1 -v2 (norm_differential_unique hN hA h1 h2).
Qed.

(** Source for [dgpr_lemma32_grad]: grad log rho_t(x) =
    sum_i D log rho_t(x)(eps_i) eps_i. *)
Lemma dgpr_lemma32_grad (x : X) : grad (t, x) = \sum_i Dh x (eps i) *: eps i.
Proof.
rewrite /dgpr_heat_grad_log_rho /dgpr_gradient_values scaler_sumr /=; apply: eq_bigr => i _.
rewrite scalerA -dgpr_lemma32_Dh_rho mulKf //; exact: lt0r_neq0 (dgpr_lemma32_pos x).
Qed.

(** Source for [dgpr_lemma32_Dh_inner]: D log rho_t(x)(w) =
    w . grad log rho_t(x), the gradient of Federer 1.7.4 (mr:notation). *)
Lemma dgpr_lemma32_Dh_inner (x w : X) : Dh x w = euclidean_inner_product w (grad (t, x)).
Proof.
rewrite dgpr_lemma32_grad -(dgpr_coordinate_sum (Dh x) w) (dgpr_orthonormal_inner BX heX orth).
apply: eq_bigr => i _.
by rewrite euclidean_inner_basis (dgpr_orthonormal_coefficient BX orth).
Qed.

(** Source for [dgpr_lemma32_fisher_integrand]: rho_t |grad log rho_t|^2
    = sum_j rho_t (D log rho_t(eps_j))^2 (Federer 1.7.5). *)
Lemma dgpr_lemma32_fisher_integrand (x : X) :
  rho (t, x) * N (grad (t, x)) ^+ 2 = \sum_j rho (t, x) * Dh x (eps j) ^+ 2.
Proof. by rewrite dgpr_lemma32_grad dgpr_lemma31_coordinate_norm mulr_sumr. Qed.

(** Source for [dgpr_lemma32_Q_gradient]: proof of lem:DGPR32: Q being
    symmetric, sum_j (D log rho_t(e_j))^2 = |Q(grad log rho_t)|^2, which
    is at most 16/(3 lambda^2) |B_t(grad log rho_t)|^2 by eq:32:QB. *)
Lemma dgpr_lemma32_Q_gradient (x : X) :
  \sum_j Dh x (ej j x) ^+ 2 <= chic * NY (B (t, x) (grad (t, x))) ^+ 2.
Proof.
set g := grad (t, x).
have e1 j : Dh x (ej j x) = euclidean_inner_product (Qx x g) (eps j).
  rewrite dgpr_lemma32_Dh_inner /dgpr_lemma32_e.
  have := dgpr_Q_symmetric BX hCY heX lam (B (t, x)) (eps j) g; rewrite !hom_as_linearE => ->.
  exact: (inner_symmetric BX).
rewrite (eq_bigr _ (fun j _ => congr1 (fun r => r ^+ 2) (e1 j))).
rewrite -(dgpr_orthonormal_parseval BX heX orth) (inner_norm_sqr hCY).
by have [_ h] := dgpr_Q_image BX hCY heX hlam (B (t, x)) g.
Qed.

(** Source for [dgpr_lemma32_DQ]: proof of lem:DGPR32, eq:32:DQ: at a
    point where all e_j are differentiable,
    sum_j |De_j(x)|^2 = |DQ(x)|^2 <= (2 Lambda Lip(chi))^2 |DB_t(x)|^2. *)
Lemma dgpr_lemma32_DQ (x : X) :
  (forall j, has_norm_differential N N setT (ej j) x (De j x)) ->
  \sum_j HXX (De j x) ^+ 2 <= KQ ^+ 2 * \sum_i NH (DB (t, x) (eps i)) ^+ 2.
Proof.
move=> hD.
have hK := dgpr_lemma32_K_ge0.
have hF : dgpr_differential_values HXX Qx x (fun v => dgpr_frame (fun j => De j x v)).
  by apply: dgpr_frame_values => j; exists (De j x); split => //; exact: hD j.
have hv v : HXX (dgpr_frame (fun j => De j x v)) <= KQ * NH (DB (t, x) v).
  exact: (dgpr_values_compare hHXX hNH v hK hF (hDB x) (fun y => dgpr_lemma32_Q_difference y x)).
have e1 : \sum_j HXX (De j x) ^+ 2 = \sum_i HXX (dgpr_frame (fun j => De j x (eps i))) ^+ 2.
  rewrite (eq_bigr (fun j => \sum_i N (De j x (eps i)) ^+ 2)) => [|j _].
    by rewrite exchange_big; apply: eq_bigr => i _; rewrite dgpr_frame_sqr.
  rewrite (dgpr_hom_norm_sqr BX BX heX _ heX orth); apply: eq_bigr => i _.
  by rewrite (inner_norm_sqr BX).
rewrite e1 mulr_sumr; apply: ler_sum => i _.
have h := hv (eps i).
have h0 : 0 <= HXX (dgpr_frame (fun j => De j x (eps i))) := inner_norm_nonnegative _ _.
have := ler_pM h0 h0 h h.
by rewrite -!expr2 exprMn.
Qed.

(** Source for [dgpr_lemma32_integrand]: proof of lem:DGPR32: at a point
    where all e_j are differentiable,
    sum_j rho_t [(div e_j + D log rho_t(e_j))^2 - trace(De_j o De_j)]
    <= C_1 rho_t (|DB_t|^2 + |B_t(grad log rho_t)|^2), by
    (div D)^2 <= n |D|^2, |trace(D o D)| <= |D|^2, eq:32:QB and eq:32:DQ. *)
Lemma dgpr_lemma32_integrand (x : X) :
  (forall j, has_norm_differential N N setT (ej j) x (De j x)) ->
  \sum_j rho (t, x) * ((dgpr_divergence (De j x) + Dh x (ej j x)) ^+ 2 -
    dgpr_divergence (hom_comp (De j x) (De j x))) <=
  C1 * dgpr_lemma31_integrand hS DB (t, x).
Proof.
move=> hD.
have hr := dgpr_lemma32_pos x.
have hj j : (dgpr_divergence (De j x) + Dh x (ej j x)) ^+ 2 -
    dgpr_divergence (hom_comp (De j x) (De j x)) <=
    (2 * n%:R + 1) * HXX (De j x) ^+ 2 + 2 * Dh x (ej j x) ^+ 2.
  have h1 := dgpr_divergence_sqr (De j x).
  have h2 := dgpr_divergence_comp (De j x).
  have h3 := ler_norm (- dgpr_divergence (hom_comp (De j x) (De j x))).
  rewrite normrN in h3.
  move: h1 h2 h3; set a := dgpr_divergence (De j x); set b := Dh x (ej j x).
  set s := dgpr_divergence _; set D2 := HXX (De j x) ^+ 2 => h1 h2 h3.
  have hab : (a + b) ^+ 2 <= 2 * a ^+ 2 + 2 * b ^+ 2.
    have := sqr_ge0 (a - b); rewrite !expr2 => hh; nra.
  lra.
have hsum : \sum_j ((dgpr_divergence (De j x) + Dh x (ej j x)) ^+ 2 -
    dgpr_divergence (hom_comp (De j x) (De j x))) <=
    \sum_j ((2 * n%:R + 1) * HXX (De j x) ^+ 2 + 2 * Dh x (ej j x) ^+ 2).
  by apply: ler_sum => j _; exact: hj j.
rewrite [X in _ <= X]big_split /= -!mulr_sumr in hsum.
have hDQ := dgpr_lemma32_DQ hD.
have hQg := dgpr_lemma32_Q_gradient x.
rewrite /dgpr_lemma31_integrand -mulr_sumr [C1 * (rho (t, x) * _)]mulrCA.
apply: ler_wpM2l; first exact: ltW.
move: hsum hDQ hQg.
set P := \sum_j HXX (De j x) ^+ 2; set G := \sum_j Dh x (ej j x) ^+ 2.
set SD := \sum_i NH (DB (t, x) (eps i)) ^+ 2; set Bg := NY _ ^+ 2.
set S0 := \sum_j _ => hsum hDQ hQg.
have hK2 : 0 <= KQ ^+ 2 := sqr_ge0 _.
have hc : 0 <= chic := ltW (dgpr_chi_constant_gt0 hlam).
have hn : 0 <= 2 * n%:R + 1 :> R by rewrite addr_ge0 // mulr_ge0.
have hSD : 0 <= SD by apply: sumr_ge0 => i _; exact: sqr_ge0.
have hBg : 0 <= Bg := sqr_ge0 _.
have h1 := ler_wpM2l hn hDQ.
have h2 := mulr_ge0 (mulr_ge0 hn hK2) hBg.
have h3 := mulr_ge0 hc hSD.
rewrite /dgpr_lemma32_C1.
have e : ((2 * n%:R + 1) * KQ ^+ 2 + 2 * chic) * (SD + Bg) =
    (2 * n%:R + 1) * (KQ ^+ 2 * SD) + (2 * n%:R + 1) * KQ ^+ 2 * Bg + 2 * (chic * SD) +
    2 * (chic * Bg) by ring.
rewrite e; nra.
Qed.

(** Source for [dgpr_lemma32_fixed_time]: blueprint proof of lem:DGPR32,
    eq:32:I at a fixed time t < T:
    I(rho_t) <= (n - m) gamma/(2(T - t)) + (n/2) m(t)
                + C_1 ∫ rho_t (|DB_t|^2 + |B_t(grad log rho_t)|^2) dL^n,
    the last integral being the upper integral of Federer 2.4.2. *)
Theorem dgpr_lemma32_fixed_time :
  (dgpr_fisher_information hS t <=
    ((n - m)%N%:R * gamma / (2 * (T - t)) + n%:R / 2 * dgpr_lemma31_m delta T gamma t)%:E +
    C1%:E * measure_upper_integral LL
      (real_total_integrand (fun x => dgpr_lemma31_integrand hS DB (t, x))))%E.
Proof.
have hnm : (n - m)%N%:R = n%:R - m%:R :> R by rewrite natrB //; case/andP: hm.
rewrite hnm.
have hgauss := dgpr_lemma32_gauss.
have hpos := dgpr_lemma32_pos.
have hDh := dgpr_lemma32_DhP.
have hD2h := dgpr_lemma32_D2hP.
(* the constant fields eps_j *)
have hd0 : dgpr_divergence (0 : Hom X X) = 0.
  have h := dgpr_divergence_sqr (0 : Hom X X).
  rewrite /hom_norm inner_norm0 expr0n /= mulr0 in h.
  have h2 : dgpr_divergence (0 : Hom X X) ^+ 2 = 0 by apply/eqP; rewrite eq_le h sqr_ge0.
  by move/eqP: h2; rewrite sqrf_eq0 => /eqP.
have hc00 : hom_comp (0 : Hom X X) (0 : Hom X X) = 0.
  by apply: hom_ext => v; rewrite hom_compE !hom_zeroE.
have hfa j : exists a : R,
    is_measure_integral LL (real_total_integrand (fun x => - (rho (t, x) * hess x (eps j)))) a%:E /\
    is_measure_integral LL (real_total_integrand (fun x => rho (t, x) * Dh x (eps j) ^+ 2)) a%:E.
  have [_ hI] := dgpr_ibp hgauss hpos hrho_logpoly (dgpr_lemma32_constant_growth j) hDh hD2h.
  have hae : measure_almost_everywhere LL
      [set x | has_norm_differential N N setT (fun _ : X => eps j) x 0].
    apply: (measure_almost_everywhere_mono hLL _ (measure_almost_everywhere_true hLL)) => x _.
    have hi : norm_domain_interior N setT x by exists 1; split.
    exact: (@norm_differential_constant R X X N N hN hN setT x (eps j) hi).
  have [a [h1 h2]] := hI (fun _ => 0) hae.
  exists a; split; first exact: h1.
  have -> : (fun x => rho (t, x) * Dh x (eps j) ^+ 2) = (fun x => rho (t, x) *
      ((dgpr_divergence (0 : Hom X X) + Dh x (eps j)) ^+ 2 -
        dgpr_divergence (hom_comp (0 : Hom X X) (0 : Hom X X)))).
    by apply: funext => x; rewrite hc00 hd0 add0r subr0.
  exact: h2.
have [a ha] := choice hfa.
(* the fields e_j *)
have hfb j : exists b : R,
    is_measure_integral LL (real_total_integrand (fun x => - (rho (t, x) * hess x (ej j x)))) b%:E /\
    is_measure_integral LL (real_total_integrand (fun x => rho (t, x) *
      ((dgpr_divergence (De j x) + Dh x (ej j x)) ^+ 2 -
        dgpr_divergence (hom_comp (De j x) (De j x))))) b%:E /\
    measure_almost_everywhere LL [set x | has_norm_differential N N setT (ej j) x (De j x)].
  have [hae hI] := dgpr_ibp hgauss hpos hrho_logpoly (dgpr_lemma32_e_growth j) hDh hD2h.
  have hDe : measure_almost_everywhere LL [set x | has_norm_differential N N setT (ej j) x (De j x)].
    by apply: (measure_almost_everywhere_mono hLL _ hae) => x hx; exact: xgetPex hx.
  have [b [h1 h2]] := hI (De j) hDe.
  by exists b.
have [b hb] := choice hfb.
(* I(rho_t) *)
have hFI : dgpr_fisher_information hS t = (\sum_j a j)%:E.
  rewrite /dgpr_fisher_information.
  have -> : (fun x => rho (t, x) * N (grad (t, x)) ^+ 2) =
      (fun x => \sum_j rho (t, x) * Dh x (eps j) ^+ 2).
    by apply: funext => x; exact: dgpr_lemma32_fisher_integrand.
  apply: dgpr_upper_integral_value.
  exact: (dgpr_integral_sum hLL (fun j => (ha j).2)).
(* the pointwise inequality and its integral *)
have [e [he hem]] := dgpr_lemma31_min_integral hS ht.
have [_ _ _ hrho] := dgpr_identities_mass hS ht.
pose c := (2 * (T - t))^-1.
have hpt x : \sum_j - (rho (t, x) * hess x (eps j)) <=
    (c * ((n%:R - m%:R) * rho (t, x)) + n%:R / 2 * emin (t, x)) +
    \sum_j - (rho (t, x) * hess x (ej j x)).
  have hsp := dgpr_lemma32_split x.
  have htt := dgpr_lemma32_trace_term x.
  have hm1 := ler_wpM2l (ltW (hpos x)) hsp.
  have e1 : \sum_j - (rho (t, x) * hess x (eps j)) = rho (t, x) * \sum_j - hess x (eps j).
    by rewrite mulr_sumr; apply: eq_bigr => j _; rewrite mulrN.
  have e2 : \sum_j - (rho (t, x) * hess x (ej j x)) = - (rho (t, x) * \sum_j hess x (ej j x)).
    by rewrite mulr_sumr -sumrN.
  rewrite e1 e2; rewrite mulrBr in hm1; rewrite -/c in hm1 htt; lra.
have hL := dgpr_integral_sum hLL (fun j => (ha j).1).
have hR1 := real_total_integral_scale hLL c
  (real_total_integral_scale hLL (n%:R - m%:R) hrho).
have hR2 := real_total_integral_scale hLL (n%:R / 2) he.
have hR3 := dgpr_integral_sum hLL (fun j => (hb j).1).
have hR := real_total_integral_add hLL (real_total_integral_add hLL hR1 hR2) hR3.
have hle := dgpr_integral_le hLL hpt hL hR.
(* the integrals b_j *)
have hB := dgpr_integral_sum hLL (fun j => (hb j).2.1).
have hae := dgpr_almost_everywhere_finite hLL (fun j => (hb j).2.2).
have hUI : ((\sum_j b j)%:E <= C1%:E * measure_upper_integral LL
    (real_total_integrand (fun x => dgpr_lemma31_integrand hS DB (t, x))))%E.
  rewrite -(dgpr_upper_integral_value hB) -(dgpr_upper_integral_scale hLL _ dgpr_lemma32_C1_gt0).
  apply: (dgpr_upper_integral_ae_le hLL).
  by apply: (measure_almost_everywhere_mono hLL _ hae) => x hx; exact: dgpr_lemma32_integrand.
(* conclusion *)
rewrite hFI.
have hm' : (n%:R - m%:R) * gamma / (2 * (T - t)) = c * ((n%:R - m%:R) * gamma).
  by rewrite /c mulrC.
have hn2 : n%:R / 2 * e <= n%:R / 2 * dgpr_lemma31_m delta T gamma t.
  by apply: ler_wpM2l => //; rewrite divr_ge0.
apply: (@le_trans _ _ (((c * ((n%:R - m%:R) * gamma) + n%:R / 2 * e)%:E + (\sum_j b j)%:E)%E)).
  by rewrite -EFinD lee_fin.
apply: leeD => //; rewrite lee_fin hm'; lra.
Qed.
End Lemma32.
