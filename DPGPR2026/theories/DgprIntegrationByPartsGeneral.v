(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    section 3, lem:ibp, DPGPR (3.17), with the hypotheses of the
    blueprint: rho of class infinity, positive, of Gaussian decay, with
    D log rho of polynomial growth, and e locally Lipschitzian of
    polynomial growth. Following the general case of the blueprint proof,
    [dgpr_ibp_smooth] is applied to the smoothings e_eps, eps = 1/(k + 2),
    of Federer 4.1.2, and the limit is taken with Lebesgue's bounded
    convergence theorem (Federer 2.4.9, p. 85). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP RealMetricBackground NormMetric GrassmannAbbreviations
  EuclideanInnerProduct InnerProductUP InnerNorm HilbertFormCompactness FiniteCoordinates
  EuclideanCoordinateMetric
  NormDifferentialUP NormDifferentialDirectional NormClassOneUP NormRegularity
  EuclideanLebesgueDimensions PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  PartialAbsolutePartsGraph PartialDominatedConvergence MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureStepIntegralIdentification MeasurableTotalLimits RealTotalMeasurabilityProjection
  SummableRealFunctionUP ExtendedRealOrderLimit RealErrorOrderLimit RealDominatedIntegralLimit
  MeasureBoundedConvergence Smoothing ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm ContinuousMultilinearOne
  MultilinearSuccessorArguments NormHigherDifferentialUP NormClassHigherUP
  RealExponentialUP RealExponentialSealed RealExponentialLaws.
From DPGPR Require Import DgprGrowthClasses DgprLebesgueIntegrals DgprDifferentialCalculus
  DgprDivergenceIntegral DgprIntegrationByParts DgprIntegrationByPartsClasses
  DgprLipschitzSmoothing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section General.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Local Notation pw := dgpr_polynomial_weight.
Local Notation gw := dgpr_gaussian_weight.
Local Notation NR := (fun t : R^o => `|t|).
Local Notation hNR := (@scalar_absolute_value_norm R).
Local Notation E := (@RealExponential.exponential R).
Local Notation L := (@RealExponential.logarithm R).
Local Notation hE := (@RealExponential.laws R).
Local Notation eps := (@coordinate_basis R n).
Local Notation ZX k := (@ContinuousMultilinear.space R k X X NX NX hNX hNX).
Local Notation evX k := (@ContinuousMultilinear.evaluation R k X X NX NX hNX hNX).
Local Notation args2 w v := (multilinear_successor_arguments [ffun _ : 'I_1 => w] v).
Local Notation ZR k := (@ContinuousMultilinear.space R k X R^o NX NR hNX hNR).
Local Notation evR k := (@ContinuousMultilinear.evaluation R k X R^o NX NR hNX hNR).

(** Source for [dgpr_almost_dominated_limit]: Federer 2.4.9, p. 85
    (Lebesgue's bounded convergence theorem), with 2.3.2(6), pp. 73-74:
    if F_k -> f everywhere and G_k -> g at L^n almost all points, all
    dominated by one L^n summable function, and if the integrals of F_k
    and G_k have a common value a_k, then the integrals of f and g exist
    and have a common value. *)
Lemma dgpr_almost_dominated_limit (F G : nat -> X -> R) (f g H : X -> R) (a : nat -> R)
    (P : set X) :
  summable_real_functions mu H ->
  (forall k x, `|F k x| <= H x) -> (forall k x, `|G k x| <= H x) ->
  (forall x t, 0 < t -> exists N, forall k, (N <= k)%N -> `|F k x - f x| < t) ->
  measure_almost_everywhere mu P ->
  (forall x, P x -> forall t, 0 < t -> exists N, forall k, (N <= k)%N -> `|G k x - g x| < t) ->
  (forall k, is_measure_integral mu (real_total_integrand (F k)) (a k)%:E) ->
  (forall k, is_measure_integral mu (real_total_integrand (G k)) (a k)%:E) ->
  exists b : R, is_measure_integral mu (real_total_integrand f) b%:E /\
    is_measure_integral mu (real_total_integrand g) b%:E.
Proof.
move=> hH hFb hGb hFc hP hGc hFi hGi.
have hGm k : is_measure_measurable_function mu (real_total_integrand (G k)) := (hGi k).1.
have hFm k : is_measure_measurable_function mu
    (partial_function_total (F k : X -> real_line_metric R)).
  exact: (@real_total_measurability_projection R X mu hm (F k) (hFi k).1).
have hGm' k : is_measure_measurable_function mu
    (partial_function_total (G k : X -> real_line_metric R)).
  exact: (@real_total_measurability_projection R X mu hm (G k) (hGm k)).
have hgm : is_measure_measurable_function mu (real_total_integrand g).
  have h : is_measure_measurable_function mu
      (partial_function_total (g : X -> real_line_metric R)).
    apply: (@measurable_total_functions_almost_limit R _ (real_line_metric R) mu hm
      (fun k => G k : X -> real_line_metric R) g P hGm' hP).
    move=> x hx A hA.
    have [t ht hball] :=
      proj1 (metricType_numDomainType.nbhs_mdistP (g x : real_line_metric R) A) hA.
    have [N hN] := hGc x hx t ht.
    exists N=> // k hk; apply: hball.
    change (is_true (mdist (g x : real_line_metric R) (G k x) < t)).
    by rewrite real_line_metric_distanceE distrC; exact: hN.
  exact: (@measurable_partial_real_embedding R _ mu hm _ h).
have hdom k : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_extended_function_absolute_value (real_total_integrand (G k)))
    (real_total_integrand H)).
  apply: (@measure_almost_everywhere_mono R _ mu hm setT _ _
    (measure_almost_everywhere_true hm))=> x _.
  exists (`|G k x|)%:E, (H x)%:E; split.
  - exists (G k x)%:E; split; first exact/real_total_integrand_graph.
    by rewrite abse_EFin.
  - split; first exact/real_total_integrand_graph.
    by rewrite lee_fin; exact: hGb.
have hloc : measure_almost_everywhere mu (partial_extended_convergence_locus
    (fun k => real_total_integrand (G k)) (real_total_integrand g)).
  apply: (@measure_almost_everywhere_mono R _ mu hm P _ _ hP)=> x hx.
  exists (fun k => (G k x)%:E), (g x)%:E; split.
    by move=> k; exact/real_total_integrand_graph.
  split; first exact/real_total_integrand_graph.
  by apply: real_error_extended_order_limit=> t ht; exact: hGc x hx t ht.
have [a' [e' [b [hai [hgi [_ [_ hlim]]]]]]] := @measure_bounded_convergence R X mu hm
  (fun k => real_total_integrand (G k)) (real_total_integrand g) (real_total_integrand H)
  hH hGm hgm hdom hloc.
have ha k : a' k = a k by have := measure_integral_unique (hai k) (hGi k); case.
have hlim' : extended_order_limit (fun k => (a k)%:E) b%:E.
  have -> : (fun k => (a k)%:E) = (fun k => (a' k)%:E) by apply: funext=> k; rewrite ha.
  exact: hlim.
exists b; split=> //.
have hfm := dgpr_limit_measurable hFm hFc.
apply: (@real_dominated_integral_limit R _ mu hm F f H a b hH hfm hFb _ hFi hlim').
by move=> x; apply: real_error_extended_order_limit=> t ht; exact: hFc x t ht.
Qed.

(** Source for [dgpr_weight_shift]: the inequality
    c (2 + r)^c <= c' (1 + r)^c' with
    c' = c 2^c, since 2 + r <= 2 (1 + r); supporting def:classes. *)
Lemma dgpr_weight_shift (c r : R) : 0 < c -> 0 <= r ->
  pw c (r + 1) <= pw (c * E (c * L 2)) r.
Proof.
move=> hc hr.
have hr1 : 0 <= r + 1 by lra.
rewrite (dgpr_polynomial_weightE _ hr1) (dgpr_polynomial_weightE _ hr).
have hl := dgpr_log_one_plus_nonnegative hr.
have hL2 : 0 <= L 2.
  by rewrite -(real_logarithm_one R) real_logarithm_order //; lra.
have hp : L (2 * (1 + r)) = L 2 + L (1 + r) by apply: real_logarithm_product; lra.
have hlog : L (1 + (r + 1)) <= L 2 + L (1 + r).
  by rewrite -hp real_logarithm_order; lra.
have hE1 : 1 <= E (c * L 2).
  rewrite -[X in X <= _](real_exponential_zero hE) real_exponential_order.
  exact: mulr_ge0 (ltW hc) hL2.
set l := L (1 + r); set q := E (c * L 2).
have h1 : E (c * L (1 + (r + 1))) <= q * E (c * l).
  rewrite /q -(real_exponential_add hE) real_exponential_order -mulrDr.
  exact: (ler_wpM2l (ltW hc) hlog).
have h2 : E (c * l) <= E (c * q * l).
  rewrite real_exponential_order; apply: ler_wpM2r=> //.
  by rewrite -{1}[c]mulr1; exact: (ler_wpM2l (ltW hc) hE1).
have hq : 0 <= q by rewrite /q; exact: ltW (dgpr_exponential_positive _).
apply: le_trans (ler_wpM2l (ltW hc) h1) _.
rewrite mulrA; apply: ler_wpM2l; first exact: mulr_ge0 (ltW hc) hq.
exact: h2.
Qed.

(** Source for [dgpr_weight_scale]: the inequality
    b c (1 + r)^c <= c' (1 + r)^c' with
    c' = b c + c; supporting def:classes. *)
Lemma dgpr_weight_scale (b c r : R) : 0 <= b -> 0 < c -> 0 <= r ->
  b * pw c r <= pw (b * c + c) r.
Proof.
move=> hb hc hr; rewrite !dgpr_polynomial_weightE //.
have hl := dgpr_log_one_plus_nonnegative hr.
have hbc : 0 <= b * c := mulr_ge0 hb (ltW hc).
have hE1 : E (c * L (1 + r)) <= E ((b * c + c) * L (1 + r)).
  by rewrite real_exponential_order; apply: ler_wpM2r=> //; lra.
have hp := dgpr_exponential_positive (c * L (1 + r)).
rewrite mulrA; apply: le_trans (_ : (b * c + c) * E (c * L (1 + r)) <= _).
  by apply: ler_wpM2r; [exact: ltW|lra].
apply: ler_wpM2l=> //; lra.
Qed.

(** Source for [dgpr_lipschitz_differential_bound]: if f is Lipschitzian
    with constant L on B(a, 1) and Df(a) exists, then |Df(a)(v)| <= L |v|,
    from the difference quotients, Federer 3.1.1, p. 209. *)
Lemma dgpr_lipschitz_differential_bound (f : X -> X) (a : X) (D : Hom X X) (Lc : R) (v : X) :
  has_norm_differential NX NX setT f a D -> 0 <= Lc ->
  (forall y z, NX (y - a) <= 1 -> NX (z - a) <= 1 -> NX (f y - f z) <= Lc * NX (y - z)) ->
  NX (D v) <= Lc * NX v.
Proof.
move=> hD hL hLip.
have hl := norm_differential_directional_limit hNX hNX hD v.
have hv := real_seminorm_nonnegative hNX.1 v.
have hd : 0 < (NX v + 1)^-1 by rewrite invr_gt0; lra.
apply: (dgpr_punctured_limit_bound hl hd)=> t /andP [ht0 htd].
have hinv : (NX v + 1)^-1 * (NX v + 1) = 1 by rewrite mulVf // gt_eqF //; lra.
have hle := ltW htd.
have h0t : 0 <= `|t| := normr_ge0 t.
have htv : NX (t *: v) <= 1 by rewrite (real_seminorm_scale hNX.1); nra.
have h1 : NX (a + t *: v - a) <= 1 by rewrite addrC addKr.
have h2 : NX (a - a) <= 1 by rewrite subrr (real_seminorm_zero hNX.1).
have hE := hLip _ _ h1 h2.
have hdv : a + t *: v - a = t *: v by rewrite addrC addKr.
rewrite hdv (real_seminorm_scale hNX.1) in hE.
rewrite (real_seminorm_scale hNX.1) normfV.
have hti : 0 <= `|t|^-1 by rewrite invr_ge0.
apply: le_trans (ler_wpM2l hti hE) _.
by rewrite [Lc * _]mulrCA mulKf //; exact: lt0r_neq0.
Qed.

(** Source for [dgpr_smooth_differentiable]: a map of class infinity is
    differentiable at every point, Federer 3.1.11, p. 219. *)
Lemma dgpr_smooth_differentiable (g : X -> X) :
  norm_class_all_orders hNX hNX setT g ->
  exists Dg : X -> Hom X X, forall x, has_norm_differential NX NX setT g x (Dg x).
Proof.
move=> hg.
have [_ [D2 [hD2 _]]] := hg 2%N.
have hD2' x : dgpr_higher_differential hNX hNX setT g 2 x (D2 x) := hD2 x Logic.I.
have [D1 hD1] := dgpr_first_from_second hD2'.
by eexists=> x; exact: dgpr_first_differential_operator (hD1 x).
Qed.

(** Source for [dgpr_smooth_fields]: for g of class infinity with
    differential Dg, the field D^2 g(x)(v, w) = E2(x)(v)(w) is the
    differential of [y ↦ Dg(y)(w)] and is symmetric (Federer 3.1.11,
    pp. 219-220); a bound on D^2 g transfers to E2. *)
Lemma dgpr_smooth_fields (g : X -> X) (Dg : X -> Hom X X) (B : X -> R) (C : R) :
  norm_class_all_orders hNX hNX setT g ->
  (forall x, has_norm_differential NX NX setT g x (Dg x)) ->
  (forall a z, dgpr_higher_differential hNX hNX setT g 2 a z ->
     forall v w, NX (evX 2 (args2 w v) z) <= C * B a * (NX v * NX w)) ->
  exists E2 : X -> Hom X (Hom X X),
    (forall x, dgpr_differential_values NX g x (fun v => Dg x v)) /\
    (forall x w, dgpr_differential_values NX (fun y => Dg y w) x (fun v => E2 x v w)) /\
    (forall x v w, E2 x v w = E2 x w v) /\
    (forall x v w, NX (E2 x v w) <= C * B x * (NX v * NX w)).
Proof.
move=> hg hDg hb.
have [_ [D2 [hD2 _]]] := hg 2%N.
have hD2' x : dgpr_higher_differential hNX hNX setT g 2 x (D2 x) := hD2 x Logic.I.
have [D1 hD1] := dgpr_first_from_second hD2'.
have hDe1 x : Dg x = @continuous_multilinear_one_operator R X X (ZX 1) NX NX
    (evX 1) (@ContinuousMultilinear.norm R 1 X X NX NX hNX hNX)
    (@ContinuousMultilinear.laws R 1 X X NX NX hNX hNX) (D1 x).
  exact: (norm_differential_unique hNX hNX (hDg x)
    (dgpr_first_differential_operator (hD1 x))).
have [Ef [hEf hEv]] := dgpr_second_differential_fields hD1 hD2'.
exists Ef; split; first by move=> x; exists (Dg x); split.
split.
  move=> x w; apply: (dgpr_values_ext _ _ (hEf x w))=> [y|v] //.
  by rewrite hDe1.
split.
  by move=> x v w; rewrite !hEv; exact: (dgpr_second_differential_symmetric v w (hD2' x)).
by move=> x v w; rewrite hEv; exact: hb x (D2 x) (hD2' x) v w.
Qed.

(** Source for [dgpr_divergence_bound]: the bound |trace D| <= n M if
    |D(v)| <= M |v| for v in R^n, Federer 1.4.5, p. 21, in the
    coordinates of 1.3.2. *)
Lemma dgpr_divergence_bound (D : Hom X X) (M : R) :
  (forall v, NX (D v) <= M * NX v) -> `|dgpr_divergence D| <= n%:R * M.
Proof.
move=> hD; rewrite dgpr_divergenceE.
apply: le_trans (ler_norm_sum _ _ _) _.
have hi i : `|D (eps i) i| <= M.
  apply: le_trans (euclidean_coordinate_norm_bound i _) _.
  by apply: le_trans (hD _) _; rewrite euclidean_coordinate_unit_norm mulr1.
apply: le_trans (ler_sum _ (fun i _ => hi i)) _.
by rewrite big_const_ord iter_addr addr0 [X in _ <= X]mulr_natl.
Qed.

(** Source for [dgpr_divergence_difference]: the bound
    |trace D - trace D'| <= n d
    if |D(v) - D'(v)| <= d |v| for v in R^n; as in
    [dgpr_divergence_bound]. *)
Lemma dgpr_divergence_difference (D D' : Hom X X) (d : R) :
  (forall v, NX (D v - D' v) <= d * NX v) ->
  `|dgpr_divergence D - dgpr_divergence D'| <= n%:R * d.
Proof.
move=> hD; rewrite !dgpr_divergenceE -sumrB.
apply: le_trans (ler_norm_sum _ _ _) _.
have hi i : `|D (eps i) i - D' (eps i) i| <= d.
  have -> : D (eps i) i - D' (eps i) i = (D (eps i) - D' (eps i)) i by rewrite !ffunE.
  apply: le_trans (euclidean_coordinate_norm_bound i _) _.
  by apply: le_trans (hD _) _; rewrite euclidean_coordinate_unit_norm mulr1.
apply: le_trans (ler_sum _ (fun i _ => hi i)) _.
by rewrite big_const_ord iter_addr addr0 [X in _ <= X]mulr_natl.
Qed.

(** Source for [dgpr_basis_difference]: the bound |D(v) - D'(v)| <= n t |v| if
    |D(e_i) - D'(e_i)| <= t for the standard basis e_1, ..., e_n of R^n,
    Federer 1.3.2, p. 14. *)
Lemma dgpr_basis_difference (D D' : Hom X X) (t : R) (v : X) :
  0 <= t -> (forall i, NX (D (eps i) - D' (eps i)) <= t) ->
  NX (D v - D' v) <= n%:R * t * NX v.
Proof.
move=> ht hD.
rewrite -(dgpr_coordinate_sum D v) -(dgpr_coordinate_sum D' v) -sumrB.
apply: le_trans (real_seminorm_sum hNX.1 _) _.
have hi i : NX (v i *: D (eps i) - v i *: D' (eps i)) <= t * NX v.
  rewrite -scalerBr (real_seminorm_scale hNX.1) mulrC.
  apply: ler_pM=> //; first exact: real_seminorm_nonnegative hNX.1 _.
  exact: euclidean_coordinate_norm_bound.
apply: le_trans (ler_sum _ (fun i _ => hi i)) _.
by rewrite big_const_ord iter_addr addr0 -mulrA [X in _ <= X]mulr_natl.
Qed.

(** Source for [dgpr_quadratic_difference]: for a bilinear form H with
    |H(v)(w)| <= M |v| |w| and |y|, |y'| <= M,
    |H(y)(y) - H(y')(y')| <= 2 M^2 |y - y'|. *)
Lemma dgpr_quadratic_difference (H : Hom X (Hom X R^o)) (y y' : X) (M d : R) :
  0 <= M -> (forall v w, `|H v w| <= M * (NX v * NX w)) ->
  NX y <= M -> NX y' <= M -> NX (y - y') <= d ->
  `|H y y - H y' y'| <= 2 * (M * M) * d.
Proof.
move=> hM hH hy hy' hyy.
have hN := real_seminorm_nonnegative hNX.1.
have h1 : H (y - y') y = H y y - H y' y by rewrite linearB.
have h2 : H y' (y - y') = H y' y - H y' y' by rewrite linearB.
have -> : H y y - H y' y' = H (y - y') y + H y' (y - y') by rewrite h1 h2; ring.
apply: le_trans (ler_normD _ _) _.
have e1 : `|H (y - y') y| <= M * (d * M).
  apply: le_trans (hH _ _) _; apply: (ler_wpM2l hM).
  by apply: ler_pM=> //; exact: hN.
have e2 : `|H y' (y - y')| <= M * (M * d).
  apply: le_trans (hH _ _) _; apply: (ler_wpM2l hM).
  by apply: ler_pM=> //; exact: hN.
have -> : 2 * (M * M) * d = M * (d * M) + M * (M * d) by ring.
exact: lerD.
Qed.

(** Source for [dgpr_integrand_difference]: the integrand
    (trace D + h(y))^2 - trace(D ∘ D) of DPGPR (3.17) depends in a
    Lipschitzian way on (D, y), uniformly for D, y bounded by M. *)
Lemma dgpr_integrand_difference (D D' : Hom X X) (y y' : X) (h : Hom X R^o) (M d : R) :
  0 <= M -> 0 <= d ->
  (forall v, NX (D v) <= M * NX v) -> (forall v, NX (D' v) <= M * NX v) ->
  NX y <= M -> NX y' <= M -> (forall v, `|h v| <= M * NX v) ->
  (forall v, NX (D v - D' v) <= d * NX v) -> NX (y - y') <= d ->
  `|((dgpr_divergence D + h y) ^+ 2 - dgpr_divergence (hom_comp D D)) -
    ((dgpr_divergence D' + h y') ^+ 2 - dgpr_divergence (hom_comp D' D'))| <=
    ((n%:R + M) * (2 * (n%:R * M + M * M)) + n%:R * (2 * M)) * d.
Proof.
move=> hM hd hD hD' hy hy' hh hDD hyy.
have hN := real_seminorm_nonnegative hNX.1.
have hn : 0 <= n%:R :> R := ler0n _ _.
have h1 := dgpr_divergence_difference hDD.
have h2 : `|h y - h y'| <= M * d.
  by rewrite -linearB; apply: le_trans (hh _) _; exact: (ler_wpM2l hM hyy).
have hb1 : `|dgpr_divergence D + h y| <= n%:R * M + M * M.
  apply: le_trans (ler_normD _ _) _; apply: lerD; first exact: dgpr_divergence_bound hD.
  by apply: le_trans (hh _) _; exact: (ler_wpM2l hM hy).
have hb2 : `|dgpr_divergence D' + h y'| <= n%:R * M + M * M.
  apply: le_trans (ler_normD _ _) _; apply: lerD; first exact: dgpr_divergence_bound hD'.
  by apply: le_trans (hh _) _; exact: (ler_wpM2l hM hy').
set b := dgpr_divergence D + h y; set b' := dgpr_divergence D' + h y'.
have hbb : `|b - b'| <= (n%:R + M) * d.
  have -> : b - b' = (dgpr_divergence D - dgpr_divergence D') + (h y - h y').
    by rewrite /b /b'; ring.
  by apply: le_trans (ler_normD _ _) _; rewrite mulrDl; exact: lerD.
have hsq : `|b ^+ 2 - b' ^+ 2| <= (n%:R + M) * d * (2 * (n%:R * M + M * M)).
  have -> : b ^+ 2 - b' ^+ 2 = (b - b') * (b + b') by ring.
  rewrite normrM; apply: ler_pM; [exact: normr_ge0|exact: normr_ge0|exact: hbb|].
  by apply: le_trans (ler_normD _ _) _; lra.
have hcomp v : NX (hom_comp D D v - hom_comp D' D' v) <= (2 * M * d) * NX v.
  rewrite !hom_compE.
  have -> : D (D v) - D' (D' v) = D (D v - D' v) + (D (D' v) - D' (D' v)).
    by rewrite linearB /= addrA subrK.
  apply: le_trans (real_seminorm_triangle hNX.1 _ _) _.
  have e1 : NX (D (D v - D' v)) <= M * (d * NX v).
    by apply: le_trans (hD _) _; exact: (ler_wpM2l hM (hDD v)).
  have e2 : NX (D (D' v) - D' (D' v)) <= d * (M * NX v).
    by apply: le_trans (hDD _) _; exact: (ler_wpM2l hd (hD' v)).
  have -> : 2 * M * d * NX v = M * (d * NX v) + d * (M * NX v) by ring.
  exact: lerD.
have h3 := dgpr_divergence_difference hcomp.
have -> : (b ^+ 2 - dgpr_divergence (hom_comp D D)) - (b' ^+ 2 - dgpr_divergence (hom_comp D' D')) =
    (b ^+ 2 - b' ^+ 2) - (dgpr_divergence (hom_comp D D) - dgpr_divergence (hom_comp D' D')).
  by ring.
apply: le_trans (ler_normB _ _) _.
have -> : ((n%:R + M) * (2 * (n%:R * M + M * M)) + n%:R * (2 * M)) * d =
    (n%:R + M) * d * (2 * (n%:R * M + M * M)) + n%:R * (2 * M * d) by ring.
exact: lerD.
Qed.

(** Source for [dgpr_integrand_bound]: with W = n + 1 + M,
    |(trace D + h(y))^2 - trace(D ∘ D)| <= 2 W^4 and |H(y)(y)| <= 2 W^4
    if D, y, h, H are bounded by M; supporting lem:ibp. *)
Lemma dgpr_integrand_bound (D : Hom X X) (y : X) (h : Hom X R^o) (H : Hom X (Hom X R^o))
    (M : R) :
  0 <= M -> (forall v, NX (D v) <= M * NX v) -> NX y <= M ->
  (forall v, `|h v| <= M * NX v) -> (forall v w, `|H v w| <= M * (NX v * NX w)) ->
  `|(dgpr_divergence D + h y) ^+ 2 - dgpr_divergence (hom_comp D D)| <=
    2 * (n%:R + 1 + M) ^+ 4 /\
  `|H y y| <= 2 * (n%:R + 1 + M) ^+ 4.
Proof.
move=> hM hD hy hh hH.
have hN := real_seminorm_nonnegative hNX.1.
have hn : 0 <= n%:R :> R := ler0n _ _.
set W := n%:R + 1 + M.
have hW1 : 1 <= W by rewrite /W; lra.
have hW0 : 0 <= W by lra.
have hMW : M <= W by rewrite /W; lra.
have hW2 : (n%:R + M) * M <= W ^+ 2.
  by rewrite expr2; apply: ler_pM=> //; [lra|rewrite /W; lra].
have hW34 : W ^+ 3 <= W ^+ 4 by apply: ler_weXn2l.
have hW23 : W ^+ 2 <= W ^+ 3 by apply: ler_weXn2l.
have hb : `|dgpr_divergence D + h y| <= W ^+ 2.
  apply: le_trans (ler_normD _ _) _; apply: le_trans _ hW2.
  rewrite mulrDl; apply: lerD; first exact: dgpr_divergence_bound hD.
  by apply: le_trans (hh _) _; exact: (ler_wpM2l hM hy).
have hb2 : `|(dgpr_divergence D + h y) ^+ 2| <= W ^+ 4.
  rewrite normrX (_ : 4 = 2 * 2)%N // exprM.
  by apply: lerXn2r; rewrite ?nnegrE ?exprn_ge0 //; exact: normr_ge0.
have hDD v : NX (hom_comp D D v) <= M * M * NX v.
  rewrite hom_compE; apply: le_trans (hD _) _; rewrite -mulrA.
  exact: (ler_wpM2l hM (hD v)).
have hdd : `|dgpr_divergence (hom_comp D D)| <= W ^+ 4.
  have hnW : n%:R <= W by rewrite /W; lra.
  have hMM : M * M <= W ^+ 2 by rewrite expr2; apply: ler_pM.
  apply: le_trans (dgpr_divergence_bound hDD) _; apply: le_trans hW34.
  rewrite exprS; apply: ler_pM; [exact: hn|exact: (mulr_ge0 hM hM)|exact: hnW|exact: hMM].
split.
  apply: le_trans (ler_normB _ _) _.
  have -> : 2 * W ^+ 4 = W ^+ 4 + W ^+ 4 by ring.
  exact: lerD.
apply: le_trans (hH _ _) _.
have hyW : NX y <= W by lra.
have h3 : M * (NX y * NX y) <= W ^+ 3.
  rewrite exprS expr2; apply: ler_pM; [exact: hM|exact: mulr_ge0 (hN _) (hN _)|exact: hMW|].
  by apply: ler_pM; [exact: hN|exact: hN|exact: hyW|exact: hyW].
have h4 : 0 <= W ^+ 4 := exprn_ge0 4 hW0.
lra.
Qed.

(** Source for [dgpr_inverse_small]: the inequality K/(k + 2) < t for all large
    natural numbers k (archimedean property). *)
Lemma dgpr_inverse_small (K t : R) : 0 < t ->
  exists N, forall k : nat, (N <= k)%N -> K * (k.+2%:R)^-1 < t.
Proof.
move=> ht.
have h0 : 0 <= `|K| / t by rewrite divr_ge0 // ltW.
exists (Num.bound (`|K| / t))=> k hk.
have hk1 : `|K| / t < k.+2%:R.
  apply: lt_le_trans (archi_boundP h0) _; rewrite ler_nat.
  exact: leq_trans hk (leq_trans (leqnSn k) (leqnSn k.+1)).
have hpos : 0 < k.+2%:R :> R by rewrite ltr0n.
have h2 : `|K| < k.+2%:R * t by rewrite -ltr_pdivrMr.
have hi : 0 <= (k.+2%:R : R)^-1 by rewrite invr_ge0 ltW.
apply: le_lt_trans (_ : K * (k.+2%:R)^-1 <= `|K| * (k.+2%:R)^-1) _.
  exact: (ler_wpM2r hi (ler_norm K)).
by rewrite ltr_pdivrMr // mulrC.
Qed.

(** Source for [dgpr_ibp_fields]: lem:ibp, DPGPR (3.17), general case
    (blueprint proof, second case), for rho given through the fields
    H1 = D log rho and H2 = D^2 log rho as in [dgpr_ibp_smooth]: if e is
    locally Lipschitzian of polynomial growth (def:classes) and De(x) is
    the differential of e at L^n almost all x, then
    - ∫ rho H2(e, e) dL^n = ∫ rho [(div e + H1(e))^2 - trace(De ∘ De)] dL^n.
    The proof applies [dgpr_ibp_smooth] to the smoothings e_eps of
    Federer 4.1.2 with eps = 1/(k + 2), and passes to the limit by
    Federer 2.4.9, using De_eps -> De at L^n almost all points
    ([dgpr_smoothing_differential_ae]). *)
Theorem dgpr_ibp_fields (rho : X -> R) (H1 : X -> Hom X R^o) (H2 : X -> Hom X (Hom X R^o))
    (e : X -> X) (De : X -> Hom X X) (c : R) :
  0 < c -> (forall x, 0 < rho x) ->
  (forall x, rho x <= gw c (NX x)) ->
  (forall x, dgpr_differential_values NR rho x (fun v => rho x * H1 x v)) ->
  (forall x w, dgpr_differential_values NR (fun y => H1 y w) x (fun v => H2 x v w)) ->
  (forall v w, norm_class_zero NX NR setT (fun x => H2 x v w)) ->
  (forall x v w, `|H1 x v| <= pw c (NX x) * NX v /\
     `|H2 x v w| <= pw c (NX x) * (NX v * NX w)) ->
  dgpr_lipschitz_polynomial_growth e ->
  measure_almost_everywhere mu [set x | has_norm_differential NX NX setT e x (De x)] ->
  exists a : R,
    is_measure_integral mu (real_total_integrand
      (fun x => - (rho x * H2 x (e x) (e x)))) a%:E /\
    is_measure_integral mu (real_total_integrand
      (fun x => rho x * ((dgpr_divergence (De x) + H1 x (e x)) ^+ 2 -
        dgpr_divergence (hom_comp (De x) (De x))))) a%:E.
Proof.
move=> hc hpos hgauss hrho hH1 hH2c hbH [ce [hce hb]] hDe.
have hN := real_seminorm_nonnegative hNX.1.
have hn : 0 <= n%:R :> R := ler0n _ _.
pose c1 := ce * E (ce * L 2).
have hq1 : 1 <= E (ce * L 2).
  rewrite -[X in X <= _](real_exponential_zero hE) real_exponential_order.
  apply: mulr_ge0; first exact: ltW.
  by rewrite -(real_logarithm_one R) real_logarithm_order //; lra.
have hc1 : 0 < c1 by rewrite /c1; apply: mulr_gt0=> //; exact: dgpr_exponential_positive.
have hcec1 : ce <= c1 by rewrite /c1 -{1}[ce]mulr1; exact: (ler_wpM2l (ltW hce) hq1).
pose C := c + c1.
have hC : 0 < C by rewrite /C; lra.
have hcC : c <= C by rewrite /C; lra.
have hc1C : c1 <= C by rewrite /C; lra.
pose P x := pw C (NX x).
have hP0 x : 0 <= P x := dgpr_polynomial_weight_nonnegative (NX x) (ltW hC).
have hPc x : pw c (NX x) <= P x := dgpr_polynomial_weight_constant (ltW hc) hcC (hN x).
have hPc1 x : pw c1 (NX x) <= P x := dgpr_polynomial_weight_constant (ltW hc1) hc1C (hN x).
have hPce x : pw ce (NX x) <= P x.
  exact: le_trans (dgpr_polynomial_weight_constant (ltW hce) hcec1 (hN x)) (hPc1 x).
have hshift x : pw ce (NX x + 1) <= P x.
  exact: le_trans (dgpr_weight_shift hce (hN x)) (hPc1 x).
have hH1x x v : `|H1 x v| <= P x * NX v.
  by have [h _] := hbH x v 0; exact: le_trans h (ler_wpM2r (hN v) (hPc x)).
have hH2x x v w : `|H2 x v w| <= P x * (NX v * NX w).
  have [_ h] := hbH x v w.
  exact: le_trans h (ler_wpM2r (mulr_ge0 (hN v) (hN w)) (hPc x)).
have be x : NX (e x) <= P x.
  by have [Lx [hL0 [hLx _]]] := hb x; apply: le_trans (hPce x); lra.
have bDe x v : has_norm_differential NX NX setT e x (De x) -> NX (De x v) <= P x * NX v.
  move=> hD; have [Lx [hL0 [hLx hLip]]] := hb x.
  apply: le_trans (dgpr_lipschitz_differential_bound v hD hL0 hLip) _.
  apply: (ler_wpM2r (hN v)); apply: le_trans (hPce x); have := hN (e x); lra.
(* the smoothings e_k = e_eps, eps = 1/(k + 2), Federer 4.1.2 *)
have [Es hEs] := dgpr_smoothing_exists hb.
pose s (k : nat) : R := (k.+2%:R)^-1.
have hs k : 0 < s k by rewrite /s invr_gt0 ltr0n.
have hs1 k : s k <= 1 by rewrite /s invf_le1 ?ler1n ?ltr0n.
pose ek k := Es (s k).
have hek k := hEs (s k) (hs k).
have hsm k := dgpr_smoothing_smooth hb (hs k) (hek k).
have hex k : exists Dg : X -> Hom X X, forall x, has_norm_differential NX NX setT (ek k) x (Dg x).
  exact: dgpr_smooth_differentiable (hsm k).
have [Dk hDk] := choice hex.
have bek k x : NX (ek k x) <= P x.
  exact: le_trans (dgpr_smoothing_value_bound hce hb (hs k) (hs1 k) (hek k) x) (hshift x).
have bDk k x v : NX (Dk k x v) <= P x * NX v.
  apply: le_trans (dgpr_smoothing_differential_bound hce hb (hs k) (hs1 k) (hek k) v (hDk k x)) _.
  exact: (ler_wpM2r (hN v) (hshift x)).
pose F k x := - (rho x * H2 x (ek k x) (ek k x)).
pose G k x := rho x * ((dgpr_divergence (Dk k x) + H1 x (ek k x)) ^+ 2 -
  dgpr_divergence (hom_comp (Dk k x) (Dk k x))).
pose f x := - (rho x * H2 x (e x) (e x)).
pose g x := rho x * ((dgpr_divergence (De x) + H1 x (e x)) ^+ 2 -
  dgpr_divergence (hom_comp (De x) (De x))).
(* dgpr_ibp_smooth for each e_k *)
have hak k : exists a : R, is_measure_integral mu (real_total_integrand (F k)) a%:E /\
    is_measure_integral mu (real_total_integrand (G k)) a%:E.
  have [C2 [hC2 hsec]] := dgpr_smoothing_second_bound hce hb (hs k) (hs1 k) (hek k).
  have [E2 [hdv [hE2 [hsym hE2b]]]] := @dgpr_smooth_fields (ek k) (Dk k)
    (fun a => pw ce (NX a + 1)) C2 (hsm k) (hDk k) hsec.
  pose ck := C + (C2 * c1 + c1).
  have hC2c1 : 0 <= C2 * c1 := mulr_ge0 hC2 (ltW hc1).
  have hck : 0 < ck by rewrite /ck; lra.
  have hwk x : P x <= pw ck (NX x).
    by apply: (dgpr_polynomial_weight_constant (ltW hC) _ (hN x)); rewrite /ck; lra.
  have hck2 x : C2 * pw ce (NX x + 1) <= pw ck (NX x).
    apply: le_trans (_ : C2 * pw c1 (NX x) <= _).
      exact: (ler_wpM2l hC2 (dgpr_weight_shift hce (hN x))).
    apply: le_trans (dgpr_weight_scale hC2 hc1 (hN x)) _.
    by apply: (dgpr_polynomial_weight_constant _ _ (hN x)); rewrite /ck; lra.
  have hgk x : rho x <= gw ck (NX x).
    apply: le_trans (hgauss x) _; apply: dgpr_gaussian_weight_constant=> //.
    by rewrite /ck /C; lra.
  have hbk x v w : NX (ek k x) <= pw ck (NX x) /\ NX (Dk k x v) <= pw ck (NX x) * NX v /\
      NX (E2 x v w) <= pw ck (NX x) * (NX v * NX w) /\ `|H1 x v| <= pw ck (NX x) * NX v /\
      `|H2 x v w| <= pw ck (NX x) * (NX v * NX w).
    have hv := hN v; have hvw := mulr_ge0 (hN v) (hN w).
    split; first exact: le_trans (bek k x) (hwk x).
    split; first exact: le_trans (bDk k x v) (ler_wpM2r hv (hwk x)).
    split; first exact: le_trans (hE2b x v w) (ler_wpM2r hvw (hck2 x)).
    split; first exact: le_trans (hH1x x v) (ler_wpM2r hv (hwk x)).
    exact: le_trans (hH2x x v w) (ler_wpM2r hvw (hwk x)).
  exact: dgpr_ibp_smooth hck hpos hgk hrho hH1 hdv hE2 hsym hH2c hbk.
have [a ha] := choice hak.
(* domination *)
have h2 : (0 : R) <= 2 by lra.
have hn1 : (0 : R) < n%:R + 1 by lra.
have [cg [hcg hcgb]] := @dgpr_gaussian_absorbs R 2 (n%:R + 1) C 4 h2 hn1 hC.
have hdom x (u : R) : `|u| <= 2 * (n%:R + 1 + P x) ^+ 4 -> `|rho x * u| <= gw cg (NX x).
  move=> hu; rewrite normrM (gtr0_norm (hpos x)).
  apply: le_trans (hcgb (NX x) (hN x)).
  have hg : rho x <= gw C (NX x).
    by apply: le_trans (hgauss x) _; apply: dgpr_gaussian_weight_constant.
  have hW : 0 <= (n%:R + 1 + P x) ^+ 4 by apply: exprn_ge0; have := hP0 x; lra.
  apply: le_trans (ler_wpM2l (ltW (hpos x)) hu) _.
  have -> : rho x * (2 * (n%:R + 1 + P x) ^+ 4) = 2 * ((n%:R + 1 + P x) ^+ 4 * rho x) by ring.
  exact: (ler_wpM2l h2 (ler_wpM2l hW hg)).
have hFb k x : `|F k x| <= gw cg (NX x).
  rewrite /F /= normrN; apply: hdom.
  exact: (dgpr_integrand_bound (hP0 x) (bDk k x) (bek k x) (hH1x x) (hH2x x)).2.
have hGb k x : `|G k x| <= gw cg (NX x).
  rewrite /G /=; apply: hdom.
  exact: (dgpr_integrand_bound (hP0 x) (bDk k x) (bek k x) (hH1x x) (hH2x x)).1.
(* convergence of F_k, everywhere *)
have hFc x t : 0 < t -> exists N, forall k, (N <= k)%N -> `|F k x - f x| < t.
  move=> ht; have [Lx [hL0 [_ hLip]]] := hb x.
  have [N hN'] := dgpr_inverse_small (rho x * (2 * (P x * P x)) * Lx) ht.
  exists N=> k hk.
  have hd : NX (ek k x - e x) <= Lx * s k.
    have hX := dgpr_smoothing_distance (hs k) (hs1 k) (hek k) hLip hL0.
    exact hX.
  have hq := dgpr_quadratic_difference (hP0 x) (hH2x x) (bek k x) (be x) hd.
  have -> : F k x - f x = - (rho x * (H2 x (ek k x) (ek k x) - H2 x (e x) (e x))).
    by rewrite /F /f; ring.
  rewrite normrN normrM (gtr0_norm (hpos x)).
  apply: le_lt_trans (ler_wpM2l (ltW (hpos x)) hq) _.
  have -> : rho x * (2 * (P x * P x) * (Lx * s k)) = rho x * (2 * (P x * P x)) * Lx * s k.
    by ring.
  exact: hN' k hk.
(* convergence of G_k, at L^n almost all points *)
pose Q i := [set a | forall D, has_norm_differential NX NX setT e a D ->
  forall t, 0 < t -> exists d, 0 < d /\ forall s, 0 < s -> s < d ->
    forall D', has_norm_differential NX NX setT (Es s) a D' -> NX (D' (eps i) - D (eps i)) < t].
have hQ i : measure_almost_everywhere mu (Q i) := dgpr_smoothing_differential_ae hb (eps i) hEs.
have hQall := @measure_almost_everywhere_countable R X 'I_n mu hm setT Q
  (countableP setT) (fun i _ => hQ i).
have hPae := @measure_almost_everywhere_and R X mu hm _ _ hDe hQall.
have hGc x : ([set x | has_norm_differential NX NX setT e x (De x)] `&`
    \bigcap_(i in setT) Q i) x ->
    forall t, 0 < t -> exists N, forall k, (N <= k)%N -> `|G k x - g x| < t.
  move=> [hDx hQx] t ht.
  have [Lx [hL0 [_ hLip]]] := hb x.
  pose K := (n%:R + P x) * (2 * (n%:R * P x + P x * P x)) + n%:R * (2 * P x).
  have hM : 0 <= P x := hP0 x.
  have hK : 0 <= K.
    have h1 : 0 <= n%:R + P x by lra.
    have h2' : 0 <= 2 * (n%:R * P x + P x * P x).
      by apply: mulr_ge0; [lra|apply: addr_ge0; apply: mulr_ge0].
    have h3 : 0 <= n%:R * (2 * P x) by apply: mulr_ge0=> //; lra.
    by rewrite /K; apply: addr_ge0=> //; exact: mulr_ge0.
  have hrK : 0 <= rho x * K := mulr_ge0 (ltW (hpos x)) hK.
  have hrK1 : 0 < rho x * K + 1 by lra.
  pose d := t / (rho x * K + 1).
  have hd : 0 < d by rewrite /d divr_gt0.
  pose eta := d / (n%:R + 1).
  have heta : 0 < eta by rewrite /eta divr_gt0.
  have hneta : n%:R * eta <= d.
    rewrite /eta mulrA ler_pdivrMr // mulrC ler_pM2l //; lra.
  have hdd i : exists r, 0 < r /\ forall s, 0 < s -> s < r ->
      forall D', has_norm_differential NX NX setT (Es s) x D' ->
        NX (D' (eps i) - De x (eps i)) < eta.
    exact: hQx i Logic.I (De x) hDx eta heta.
  have [dd hdd'] := choice hdd.
  have hNi i : exists Ni, forall k : nat, (Ni <= k)%N -> 1 * (k.+2%:R)^-1 < dd i.
    exact (dgpr_inverse_small 1 (hdd' i).1).
  have [Nf hNf] := choice hNi.
  have [N2 hN2] := dgpr_inverse_small Lx hd.
  exists (maxn (\max_i Nf i) N2)=> k hk.
  have hk1 : ((\max_i Nf i) <= k)%N := leq_trans (leq_maxl _ _) hk.
  have hk2 : (N2 <= k)%N := leq_trans (leq_maxr _ _) hk.
  have hbasis i : NX (Dk k x (eps i) - De x (eps i)) <= eta.
    have hsk : s k < dd i.
      by have := hNf i k (leq_trans (leq_bigmax i) hk1); rewrite mul1r.
    exact: ltW ((hdd' i).2 (s k) (hs k) hsk (Dk k x) (hDk k x)).
  have hop v : NX (Dk k x v - De x v) <= d * NX v.
    apply: le_trans (dgpr_basis_difference v (ltW heta) hbasis) _.
    exact: (ler_wpM2r (hN v) hneta).
  have hy : NX (ek k x - e x) <= d.
    have hX := dgpr_smoothing_distance (hs k) (hs1 k) (hek k) hLip hL0.
    apply: le_trans _ (ltW (hN2 k hk2)); exact hX.
  have hdiff := dgpr_integrand_difference hM (ltW hd) (bDk k x) (fun v => bDe x v hDx)
    (bek k x) (be x) (hH1x x) hop hy.
  have hlt : rho x * (K * d) < t.
    have -> : rho x * (K * d) = t - d by rewrite /d; field; exact: (lt0r_neq0 hrK1).
    lra.
  have -> : G k x - g x = rho x * (((dgpr_divergence (Dk k x) + H1 x (ek k x)) ^+ 2 -
      dgpr_divergence (hom_comp (Dk k x) (Dk k x))) -
      ((dgpr_divergence (De x) + H1 x (e x)) ^+ 2 - dgpr_divergence (hom_comp (De x) (De x)))).
    by rewrite /G /g; ring.
  rewrite normrM (gtr0_norm (hpos x)).
  apply: le_lt_trans (ler_wpM2l (ltW (hpos x)) hdiff) _.
  exact: hlt.
have [b [hb1 hb2]] := dgpr_almost_dominated_limit (dgpr_gaussian_weight_summable n hcg)
  hFb hGb hFc hPae hGc (fun k => (ha k).1) (fun k => (ha k).2).
by exists b.
Qed.

(** Source for [dgpr_ibp]: lem:ibp, DPGPR (3.17). Let rho be of class
    infinity, positive, of Gaussian decay, with D log rho of polynomial
    growth, and let e be locally Lipschitzian of polynomial growth
    (def:classes). Then e is differentiable at L^n almost all points
    (Rademacher's theorem, Federer 3.1.6, applied on the balls
    B(0, k + 1)), and for every field De which is the differential of e at
    L^n almost all points,
    - ∫ rho D^2 log rho(e, e) dL^n
      = ∫ rho [(div e + D log rho(e))^2 - trace(De ∘ De)] dL^n,
    both integrands being L^n summable. Here Dh(x) = D log rho(x) and
    D2h(x) = D^2 log rho(x), for any such fields. *)
Theorem dgpr_ibp (rho : X -> R) (e : X -> X) (Dh : X -> Hom X R^o) (D2h : X -> ZR 2) :
  dgpr_gaussian_decay hNR rho -> (forall x, 0 < rho x) ->
  dgpr_log_derivative_polynomial_growth rho ->
  dgpr_lipschitz_polynomial_growth e ->
  (forall x, has_norm_differential NX NR setT (fun y => L (rho y)) x (Dh x)) ->
  (forall x, dgpr_higher_differential hNX hNR setT (fun y => L (rho y)) 2 x (D2h x)) ->
  measure_almost_everywhere mu [set x | norm_differentiable_at NX NX setT e x] /\
  forall De : X -> Hom X X,
    measure_almost_everywhere mu [set x | has_norm_differential NX NX setT e x (De x)] ->
    exists a : R,
      is_measure_integral mu (real_total_integrand
        (fun x => - (rho x * evR 2 [ffun _ : 'I_2 => e x] (D2h x)))) a%:E /\
      is_measure_integral mu (real_total_integrand
        (fun x => rho x * ((dgpr_divergence (De x) + Dh x (e x)) ^+ 2 -
          dgpr_divergence (hom_comp (De x) (De x))))) a%:E.
Proof.
move=> hrho hpos hlog he hDh hD2h.
have [ce [hce hb]] := he.
split; first exact: dgpr_lipschitz_differentiable_ae hb.
move=> De hDe.
have [c1 [H2 [hc1 [hrg [hdr [hH2 [hH2v [hH2c hHb]]]]]]]] :=
  dgpr_log_density_fields hrho hpos hlog hDh hD2h.
have [a [h1 h2]] := dgpr_ibp_fields hc1 hpos hrg hdr hH2 hH2c hHb he hDe.
exists a; split; last exact: h2.
have -> : (fun x => - (rho x * evR 2 [ffun _ : 'I_2 => e x] (D2h x))) =
    (fun x => - (rho x * H2 x (e x) (e x))).
  by apply: funext=> x; rewrite hH2v multilinear_successor_constant_arguments.
exact: h1.
Qed.
End General.
