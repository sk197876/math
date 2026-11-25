(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    section 3, lem:classes(cl:dt): if f : Omega_T -> R has Gaussian decay
    before T, then [t ↦ ∫ f(t,x) dL^n x] is of class 1 on R ∩ {t : t < T},
    with derivative ∫ ∂_t f(t,x) dL^n x. The statement is formalised for
    real valued f (all uses in the blueprint are real valued); see
    docs/divergences.md. Differentiation under the integral sign is
    dgpr_parameter_integral_class_one of DgprParameterIntegralDifferential. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP RealMetricBackground NormMetric GrassmannAbbreviations
  EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  ScalarInnerProduct ProductInner ProductInnerPairRegularity
  NormDifferentialUP NormDifferentialLocal NormDifferentialDirectional NormDifferentialAffineLine
  NormClassOneUP NormClassZeroPostcompose NormClassZeroArithmetic NormHigherCurveDerivativeUP
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasureIntegralUP
  MeasureIntegralUniqueness MeasureVectorIntegralUP NormClassZeroTotalMeasurable
  SummableRealFunctionUP SummableRealArithmetic ScalarVectorIntegralIdentification
  TotalVectorIntegralDomination ScalarNormMetricCompleteness LocalUniquenessExample
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  ContinuousMultilinearEvaluationBound ContinuousMultilinearZero ContinuousMultilinearOne
  NormHigherDifferentialUP NormHigherDifferentialFirst NormClassHigherUP NormRegularity
  RealExponentialUP RealExponentialSealed RealExponentialLaws.
From DPGPR Require Import DgprGrowthClasses DgprLebesgueIntegrals DgprParameterIntegralDifferential
  DgprParameterIntegralSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section TimeDerivative.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BT := (product_inner_productP (scalar_inner_productP R)
  (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm BT).
Local Notation hNT := (inner_norm_real_norm BT).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Local Notation NR := (fun t : R^o => `|t|).
Local Notation hNR := (@scalar_absolute_value_norm R).
Local Notation e0 := (((1 : R^o), (0 : X)) : TX).

(** Source for [dgpr_hom_subE]: Federer 1.1.1, p. 9: the difference
    of linear maps is computed pointwise. *)
Lemma dgpr_hom_subE (V W : lmodType R) (A B : Hom V W) v : (A - B) v = A v - B v.
Proof. by []. Qed.

(** Source for [dgpr_time_unit_norm]: Federer 1.7.11, p. 36: in the
    product inner product space R x R^n of mr:notation the vector (1,0)
    has norm 1. *)
Lemma dgpr_time_unit_norm : NT e0 = 1.
Proof.
have h := @product_first_injection_norm R R^o X _ _ (scalar_inner_productP R)
  (@euclidean_inner_productP R n) 1.
by rewrite scalar_inner_normE normr1 in h.
Qed.

(** Source for [dgpr_space_injection_norm]: Federer 1.7.11, p. 36:
    |(0,k)| = |k| in R x R^n. *)
Lemma dgpr_space_injection_norm (k : X) : NT ((0 : R^o), k) = NX k.
Proof.
exact: (@product_second_injection_norm R R^o X _ _ (scalar_inner_productP R)
  (@euclidean_inner_productP R n) k).
Qed.

(** Source for [dgpr_space_shift]: the vector operations of the
    product R x R^n, Federer 1.7.11, p. 36: (s,y) + (0,k) = (s,y+k). *)
Lemma dgpr_space_shift (s : R) (y k : X) : ((s, y) : TX) + ((0 : R^o), k) = (s, y + k).
Proof. by apply: injective_projections=> /=; rewrite ?addr0. Qed.

(** Source for [dgpr_slice_class_zero]: Federer 3.1.1, p. 210: a
    continuous map on Omega_T restricts to a continuous map on each
    time slice {t} x R^n with t < T. *)
Lemma dgpr_slice_class_zero (W : lmodType R) (NW : W -> R) (T s : R) (G : TX -> W) :
  s < T -> norm_class_zero NT NW (dgpr_before T) G ->
  norm_class_zero NX NW setT (fun y => G (s, y)).
Proof.
move=> hs hG a _; split; first by exists 1; split.
move=> e he; have [_ hc] := hG (s, a) hs.
have [d [hd h]] := hc e he.
exists d; split=> // k _ hk.
have := h ((0 : R^o), k); rewrite dgpr_space_shift dgpr_space_injection_norm.
by apply.
Qed.

(** Source for [dgpr_real_vector_integral]: Federer 4.1.2, p. 348,
    and 2.4.12, pp. 87-88: for a continuous real function on R^n
    dominated by an L^n summable function, the real integral is also the
    vector integral of 2.4.12 with values in R. *)
Lemma dgpr_real_vector_integral (F g : X -> R) (a : R) :
  norm_class_zero NX NR setT F -> summable_real_functions mu g ->
  (forall x, `|F x| <= g x) ->
  is_measure_integral mu (real_total_integrand F) a%:E ->
  is_measure_vector_integral mu
    (partial_function_total (fun x => (F x : real_norm_metric_space hNR))) a.
Proof.
move=> hF [b hb] hdom ha.
have hmeas := @norm_class_zero_total_measurable R X R^o NX NR hNX hNR mu hm
  (@euclidean_distribution_measure_open R n) F hF.
have [y [hy _]] := @dominated_total_vector_integral_exists R _ R^o NR hNR
  (@scalar_norm_metric_complete R) mu hm F g b (@scalar_norm_separable R) hmeas hb hdom.
have hr := scalar_vector_integral_identification hy.
have he := measure_integral_unique hr ha.
by case: he=> <-.
Qed.

Local Notation Zk k := (@ContinuousMultilinear.space R k TX R^o NT NR hNT hNR).
Local Notation ev k := (@ContinuousMultilinear.evaluation R k TX R^o NT NR hNT hNR).
Local Notation ZN k := (@ContinuousMultilinear.norm R k TX R^o NT NR hNT hNR).
Local Notation lawsk k := (@ContinuousMultilinear.laws R k TX R^o NT NR hNT hNR).

(** Source for [dgpr_classes_dt]: lem:classes(cl:dt), blueprint
    section 3, for real valued maps. If f : Omega_T -> R has Gaussian
    decay before T and Df is its differential, then the sections
    [x ↦ f(t,x)] and [x ↦ Df(t,x)(1,0)] are L^n summable for t < T, and
    the map I(t) = ∫ f(t,x) dL^n x is of class 1 on R ∩ {t : t < T}, with
    derivative [s ↦ s DI(t)] at t, where DI(t) = ∫ Df(t,x)(1,0) dL^n x.
    Differentiation under the integral sign is the heat-kernel worker's
    dgpr_parameter_integral_class_one (mean value theorem and Federer
    2.4.9, p. 85). *)
Theorem dgpr_classes_dt (T : R) (f : TX -> R) (Df : TX -> Hom TX R^o) :
  dgpr_gaussian_decay_before hNR T f ->
  (forall p, dgpr_before T p -> has_norm_differential NT NR (dgpr_before T) f p (Df p)) ->
  (forall t, t < T -> summable_real_functions mu (fun x => f (t, x)) /\
     summable_real_functions mu (fun x => Df (t, x) e0)) /\
  forall I DI : R -> R,
    (forall t, t < T ->
       is_measure_integral mu (real_total_integrand (fun x => f (t, x))) (I t)%:E) ->
    (forall t, t < T ->
       is_measure_integral mu (real_total_integrand (fun x => Df (t, x) e0)) (DI t)%:E) ->
    is_norm_class_one_field NR NR [set t | t < T] I (fun t => dgpr_line_hom (DI t : R^o)).
Proof.
move=> [hcls hdec] hDf.
have [hF0 [D1 [hD1 hD1c]]] := hcls 1%N.
have hZ1 := continuous_multilinear_norm_is_norm hNR (lawsk 1).
pose u : {ffun 'I_1 -> TX} := [ffun _ => e0].
pose P (p : TX) : R := ev 1 u (D1 p).
have hDfP p : dgpr_before T p -> Df p e0 = P p.
  move=> hp.
  have h1 := (@norm_higher_differential_first R TX R^o NT NR hNT hNR (fun k => Zk k)
    (fun k => ev k) (fun k => ZN k) (fun k => lawsk k) (dgpr_before T) f p (D1 p)).1 (hD1 p hp).
  by rewrite (norm_differential_unique hNT hNR (hDf p hp) h1).
have hPb p : `|P p| <= ZN 1 (D1 p).
  have hb := multilinear_operator_bound (continuous_multilinear_norm_laws (lawsk 1) (D1 p)) u.
  by rewrite big_ord1 ffunE dgpr_time_unit_norm mulr1 in hb.
have hev := continuous_multilinear_evaluation_bounded hNT (lawsk 1) u.
(* continuity of P on Omega_T *)
have hPc : norm_class_zero NT NR (dgpr_before T) P.
  exact: (@norm_class_zero_postcompose R TX (Zk 1) R^o NT (ZN 1) NR hZ1
    (dgpr_before T) D1 (ev 1 u) hD1c hev).
have hsec0 t : t < T -> exists c, 0 < c /\
    forall x, `|f (t, x)| <= dgpr_gaussian_weight c (NX x).
  move=> ht; have [c [hc hb]] := hdec 0%N t t ht.
  exists c; split=> // x.
  have [z hz] := continuous_multilinear_zero_surjective hNR (lawsk 0) (f (t, x)).
  have hHD : dgpr_higher_differential hNT hNR (dgpr_before T) f 0 (t, x) z by split.
  have := hb (t, x) z _ hHD.
  rewrite (continuous_multilinear_zero_norm hNR (lawsk 0)) hz; apply.
  by rewrite /dgpr_time_strip /= lexx.
have hsec1 a b : b < T -> exists c, 0 < c /\
    forall s x, a <= s <= b -> `|P (s, x)| <= dgpr_gaussian_weight c (NX x).
  move=> hbT; have [c [hc hb]] := hdec 1%N a b hbT.
  exists c; split=> // s x hs.
  apply: le_trans (hPb _) _; apply: (hb (s, x) (D1 (s, x)) hs).
  apply: hD1; rewrite /dgpr_before /=.
  by case/andP: hs=> _ hs; apply: le_lt_trans hs hbT.
have hlineE (c : R) (v : R^o) : dgpr_line_hom (c : R^o) v = v * c by [].
have htime s y h : ((s, y) : TX) + ((h : R^o), (0 : X)) = (s + h, y).
  by apply: injective_projections=> /=; rewrite ?addr0.
have htimeN (h : R^o) : NT (h, (0 : X)) = `|h|.
  have hh := @product_first_injection_norm R R^o X _ _ (scalar_inner_productP R)
    (@euclidean_inner_productP R n) h.
  by rewrite scalar_inner_normE in hh.
have htimeZ (h : R^o) : ((h : R^o), (0 : X)) = h *: e0.
  apply: injective_projections=> /=; last by rewrite scaler0.
  by change (h = h * 1); rewrite mulr1.
pose U : set R^o := [set s : R^o | s < T].
have hUi s : U s -> norm_domain_interior NR U s.
  move=> hs; exists (T - s); split; first by rewrite subr_gt0.
  move=> h hh; rewrite /U /=; have := ler_norm h; lra.
have hDfE s y v : U s -> Df (s, y) (v, (0 : X)) = v * P (s, y).
  by move=> hs; rewrite htimeZ linearZ /= (hDfP (s, y) hs).
(* the sections are continuous *)
have hfsec s : s < T -> norm_class_zero NX NR setT (fun y => f (s, y)).
  by move=> hs; exact: dgpr_slice_class_zero hs hF0.
have hPsec s : s < T -> norm_class_zero NX NR setT (fun y => P (s, y)).
  by move=> hs; exact: dgpr_slice_class_zero hs hPc.
split.
  move=> t ht; split.
  - have [c [hc hb]] := hsec0 t ht.
    exact: (dgpr_dominated_summable (dgpr_continuous_measurable (hfsec t ht))
      (dgpr_gaussian_weight_summable n hc) hb).
  - have [c [hc hb]] := hsec1 t t ht.
    have -> : (fun x => Df (t, x) e0) = (fun x => P (t, x)).
      by apply: funext=> x; exact: hDfP.
    apply: (dgpr_dominated_summable (dgpr_continuous_measurable (hPsec t ht))
      (dgpr_gaussian_weight_summable n hc)).
    by move=> x; apply: hb; rewrite lexx.
move=> I DI hI hDI.
apply: (@dgpr_parameter_integral_class_one R _ mu hm R^o R^o NR NR hNR hNR U
  (fun s y => f (s, y)) (fun s y => dgpr_line_hom (P (s, y) : R^o)) I
  (fun t => dgpr_line_hom (DI t : R^o)) hUi).
- move=> s hs; have [c [hc hb]] := hsec0 s hs.
  exact: (dgpr_real_vector_integral (hfsec s hs) (dgpr_gaussian_weight_summable n hc) hb (hI s hs)).
- move=> s v hs; have [c [hc hb]] := hsec1 s s hs.
  have hP := hDI s hs.
  have hPe : (fun x => Df (s, x) e0) = (fun x => P (s, x)).
    by apply: funext=> x; exact: hDfP.
  rewrite hPe in hP.
  have hvP := real_total_integral_scale hm v hP.
  have hcz : norm_class_zero NX NR setT (fun x => v * P (s, x)).
    exact: (@norm_class_zero_scale R X R^o NX NR hNR setT _ v (hPsec s hs)).
  have hg := @summable_real_scale R _ mu hm _ `|v| (dgpr_gaussian_weight_summable n hc).
  have hdom x : `|v * P (s, x)| <= `|v| * dgpr_gaussian_weight c (NX x).
    rewrite normrM; apply: ler_wpM2l; first exact: normr_ge0.
    by apply: hb; rewrite lexx.
  exact: (dgpr_real_vector_integral hcz hg hdom hvP).
- move=> y; split.
  + move=> s hs; split; first exact: hUi.
    move=> e he; have [_ hc] := hF0 (s, y) hs.
    have [d [hd hh]] := hc e he.
    exists d; split=> // h hsh hhd.
    have := hh ((h : R^o), (0 : X)); rewrite htime htimeN; apply=> //.
  + move=> s hs; split; first exact: hUi.
    * exists `|P (s, y)|; split; first exact: normr_ge0.
      by move=> h; rewrite hlineE normrM mulrC.
    * move=> e he; have [d [hd hr]] := norm_differential_remainder (hDf (s, y) hs) he.
      exists d; split=> // h hsh hhd.
      have := hr ((h : R^o), (0 : X)); rewrite htime htimeN hDfE // hlineE.
      by apply.
  + move=> s hs e he; have [_ hc] := hPc (s, y) hs.
    have [d [hd hh]] := hc e he.
    exists d; split=> // h hsh hhd v.
    rewrite dgpr_hom_subE !hlineE -mulrBr normrM mulrC.
    apply: ler_wpM2r; first exact: normr_ge0.
    by apply: ltW; have := hh ((h : R^o), (0 : X)); rewrite htime htimeN; apply.
- move=> s hs; have hs' : s < T := hs.
  pose r := (T - s) / 2.
  have hr : 0 < r by rewrite /r divr_gt0 ?subr_gt0 // ltr0n.
  have hbT : s + r < T by rewrite /r; lra.
  have [c [hc hb]] := hsec1 (s - r) (s + r) hbT.
  exists r, (fun y => dgpr_gaussian_weight c (NX y)); split=> //; split.
    exact: dgpr_gaussian_weight_summable.
  move=> h y v hh hsh; rewrite hlineE normrM mulrC.
  apply: ler_wpM2r; first exact: normr_ge0.
  apply: hb; move: hh; rewrite ltr_norml=> /andP [h1 h2].
  by apply/andP; split; lra.
Qed.


End TimeDerivative.
