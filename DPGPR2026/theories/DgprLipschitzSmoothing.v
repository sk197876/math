(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    section 3, lem:ibp, general case of the proof. For a locally
    Lipschitzian map e of polynomial growth (def:classes) the file
    constructs the smoothings e_eps = Phi_eps * e with the regularising
    kernels of Federer 4.1.2, pp. 346-347, bounds e_eps and De_eps
    uniformly for 0 < eps <= 1, and bounds D^2 e_eps for fixed eps. By
    localisation to the balls B(0, k + 1) it proves that e is
    differentiable at L^n almost all points (Rademacher's theorem,
    Federer 3.1.6, pp. 216-217) and that De_eps(x)(v) -> De(x)(v) for
    L^n almost all x (Federer 4.1.2 with 2.9.9, pp. 156-157). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric LipschitzUP MetricLocalLipschitzContinuity
  NormClassZeroWhole GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm
  InnerMetric HilbertFormCompactness FiniteCoordinates NormDifferentialUP NormClassOneUP
  NormRegularity
  EuclideanLebesgueDimensions MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP SummableRealFunctionUP Smoothing EuclideanOwnNormCompleteness
  EuclideanOwnNormSeparable ContinuousSmoothingSmoothness NormedCurveDerivativeUP
  NormDifferentialDirectional EuclideanDistributionMeasureContext NormClassZeroTotalMeasurable
  MeasureVectorIntegralUP PartialFunctionUP PartialFunctionBasic VectorDaniellHypotheses
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  MultilinearSuccessorArguments IteratedDirectionalArguments NormIteratedDirectionalUP
  NormIteratedDirectionalLaws NormHigherIteratedDirections NormHigherDifferentialUP
  UniformFunctionNormUP SummableRealArithmetic RealExponentialUP RealExponentialSealed
  RealExponentialLaws MetricClosedBalls Rademacher EuclideanClosedBallRetraction
  NormLocalLipschitzCompact CurrentMapDifferential CurrentLipschitzLebesgueActionSmoothingAE.
From DPGPR Require Import DgprGrowthClasses DgprLebesgueIntegrals DgprIntegrationByPartsClasses.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LipschitzSmoothing.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T := (real_norm_metric_space hNX).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Local Notation pw := dgpr_polynomial_weight.
Local Notation phi := (@regularising_kernel R n).
Local Notation fam := (@regularising_kernel_family R n).
Local Notation hPhi := (@regularising_kernel_laws R n).
Local Notation hFam := (@regularising_kernel_family_laws R n).
Local Notation NR := (fun t : R^o => `|t|).
Local Notation hNR := (@scalar_absolute_value_norm R).
Local Notation E := (@RealExponential.exponential R).
Local Notation hE := (@RealExponential.laws R).
Local Notation ZX k := (@ContinuousMultilinear.space R k X X NX NX hNX hNX).
Local Notation evX k := (@ContinuousMultilinear.evaluation R k X X NX NX hNX hNX).
Local Notation ZNX k := (@ContinuousMultilinear.norm R k X X NX NX hNX hNX).
Local Notation lawsX k := (@ContinuousMultilinear.laws R k X X NX NX hNX hNX).
Local Notation ZR k := (@ContinuousMultilinear.space R k X R^o NX NR hNX hNR).
Local Notation evR k := (@ContinuousMultilinear.evaluation R k X R^o NX NR hNX hNR).
Local Notation ZNR k := (@ContinuousMultilinear.norm R k X R^o NX NR hNX hNR).
Local Notation lawsR k := (@ContinuousMultilinear.laws R k X R^o NX NR hNX hNR).
Local Notation args2 w v := (multilinear_successor_arguments [ffun _ : 'I_1 => w] v).

Variable e : X -> X.
Variable c : R.
Hypothesis hc : 0 < c.
Hypothesis hb : forall x, exists L, 0 <= L /\ NX (e x) + L <= pw c (NX x) /\
  forall y z, NX (y - x) <= 1 -> NX (z - x) <= 1 -> NX (e y - e z) <= L * NX (y - z).

(** Source for [dgpr_lipschitz_local]: a locally Lipschitzian map of
    polynomial growth (def:classes) is locally Lipschitzian in the sense
    of Federer 2.2.7, p. 64. *)
Lemma dgpr_lipschitz_local : is_locally_metric_lipschitz setT (e : T -> T).
Proof.
move=> x _; have [L [hL [_ hLip]]] := hb x.
exists [set y : T | NX (y - x) < 1]; split.
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (x : T) _)).
  exists 1; first exact: ltr01.
  move=> z hz; change (is_true (NX (x - z) < 1)) in hz.
  by change (is_true (NX (z - x) < 1)); rewrite (real_seminorm_subtract hNX.1).
exists (L + 1); split; first lra.
split; first lra.
move=> y z [_ hy] [_ hz]; rewrite !real_norm_metric_distanceE.
apply: le_trans (hLip y z (ltW hy) (ltW hz)) _.
apply: ler_wpM2r; first exact: (real_seminorm_nonnegative hNX.1).
lra.
Qed.

(** Source for [dgpr_lipschitz_class_zero]: a locally Lipschitzian map
    is continuous, Federer 2.2.7, p. 64. *)
Lemma dgpr_lipschitz_class_zero : norm_class_zero NX NX setT e.
Proof.
exact: (norm_continuous_whole_class_zero
  (metric_local_lipschitz_continuous_whole dgpr_lipschitz_local)).
Qed.

(** Source for [dgpr_smoothing_exists]: the convolutions
    e_eps = Phi_eps * e of Federer 4.1.2, p. 346, exist for eps > 0,
    since e is continuous and hence locally integrable. *)
Lemma dgpr_smoothing_exists :
  exists E : R -> X -> X, forall s, 0 < s -> is_smoothing_convolution hNX (fam s) e (E s).
Proof.
have hField := @continuous_field_locally_norm_integrable R n X NX hNX e dgpr_lipschitz_class_zero.
have hex s : exists g : X -> X, 0 < s -> is_smoothing_convolution hNX (fam s) e g.
  case: (pselect (0 < s))=> hs.
  - have [g hg] := @smoothing_convolution_exists R n X NX hNX (@euclidean_own_norm_complete R n)
      (@euclidean_own_norm_separable R n) phi hPhi fam hFam s hs e hField.
    by exists g.
  - by exists (fun _ => 0)=> hs'; contradiction.
by case: (choice hex)=> E hE; exists E.
Qed.

(** Source for [dgpr_smoothing_smooth]: e_eps is of class infinity,
    Federer 4.1.2, p. 347. *)
Lemma dgpr_smoothing_smooth (s : R) (g : X -> X) :
  0 < s -> is_smoothing_convolution hNX (fam s) e g -> norm_class_all_orders hNX hNX setT g.
Proof.
move=> hs hg.
exact: (@continuous_smooth_convolution_smooth R n X NX hNX (@euclidean_own_norm_complete R n) e
  dgpr_lipschitz_class_zero (fam s) s g
  (@smoothing_dilation_smooth R n phi hPhi fam hFam s hs)
  (@smoothing_dilation_zero_beyond_radius R n phi fam hPhi hFam s hs) hg).
Qed.

(** Source for [dgpr_punctured_limit_bound]: a bound on the values
    of u(h) for small h != 0 bounds the limit, Federer 2.9.22, p. 167. *)
Lemma dgpr_punctured_limit_bound (u : R -> X) (y : X) (B d : R) :
  punctured_norm_limit NX u y -> 0 < d -> (forall t, 0 < `|t| < d -> NX (u t) <= B) ->
  NX y <= B.
Proof.
move=> hl hd hB; rewrite leNgt; apply/negP=> hlt.
have hp : 0 < NX y - B by lra.
have [d' [hd' hu]] := hl _ hp.
pose t := Num.min d d' / 2.
have hm : 0 < Num.min d d' by rewrite lt_min hd hd'.
have ht0 : 0 < t by rewrite /t divr_gt0.
have htm : t < Num.min d d' by rewrite /t ltr_pdivrMr // mulr2n; lra.
have hta : `|t| = t by rewrite ger0_norm // ltW.
have htd : t < d by apply: lt_le_trans htm _; rewrite ge_min lexx.
have htd' : t < d' by apply: lt_le_trans htm _; rewrite ge_min lexx orbT.
have hq : NX (u t) <= B by apply: hB; rewrite hta ht0 htd.
have hu' : NX (u t - y) < NX y - B by apply: hu; rewrite hta ht0 htd'.
have htri := real_seminorm_triangle hNX.1 (u t) (y - u t).
rewrite addrC subrK (real_seminorm_subtract hNX.1 y) in htri.
lra.
Qed.

(** Source for [dgpr_kernel_mean_bound]: Federer 4.1.2, p. 347: since
    Phi_eps >= 0 has integral one and vanishes outside B(0, eps), the
    integral of [z ↦ Phi_eps(z) F(z)] lies within B of a whenever
    |F(z) - a| <= B for |z| < eps. *)
Lemma dgpr_kernel_mean_bound (s : R) (F : X -> X) (y a : X) (B : R) :
  0 < s ->
  is_measure_vector_integral mu (partial_function_total (fun z => (fam s z *: F z : T))) y ->
  (forall z, NX z < s -> NX (F z - a) <= B) -> NX (y - a) <= B.
Proof.
move=> hs hy hF.
have hsm := @smoothing_dilation_smooth R n phi hPhi fam hFam s hs.
have hz := (norm_class_zeroP hNX (@scalar_absolute_value_norm R) _ _).1 (hsm 0%N).
have hmeas := @norm_class_zero_scalar_real_measurable R X NX hNX mu hm
  (@euclidean_distribution_measure_open R n) (fam s) hz.
apply: (@unit_weight_vector_error_bound R X X NX hNX mu hm (fam s) F y a B
  (@euclidean_own_norm_separable R n) hmeas
  (@smoothing_dilation_nonnegative R n phi hPhi fam hFam s hs)
  (@smoothing_dilation_integral_one R n phi fam hPhi hFam s hs) hy)=> z hz0.
exact: hF (@smoothing_dilation_nonzero_radius R n phi fam hPhi hFam s hs z hz0).
Qed.

(** Source for [dgpr_ball_norm]: the inequality |a - z| <= |a| + 1 for
    |z| <= 1. *)
Lemma dgpr_ball_norm (a z : X) : NX z <= 1 -> NX (a - z) <= NX a + 1.
Proof.
move=> hz; have := real_seminorm_triangle hNX.1 a (- z).
by rewrite (real_seminorm_negate hNX.1); lra.
Qed.

(** Source for [dgpr_growth_ball]: the bound |e(y)| + L <= c (1 + |a| + 1)^c
    for |y - a| <= 1, def:classes. *)
Lemma dgpr_growth_ball (a z : X) : NX z <= 1 ->
  exists L, 0 <= L /\ NX (e (a - z)) <= pw c (NX a + 1) /\ L <= pw c (NX a + 1) /\
    forall y w, NX (y - (a - z)) <= 1 -> NX (w - (a - z)) <= 1 ->
      NX (e y - e w) <= L * NX (y - w).
Proof.
move=> hz; have [L [hL [hLe hLip]]] := hb (a - z).
have hm : pw c (NX (a - z)) <= pw c (NX a + 1).
  apply: dgpr_polynomial_weight_monotone; first exact: ltW.
    exact: (real_seminorm_nonnegative hNX.1).
  exact: dgpr_ball_norm.
have h0 := real_seminorm_nonnegative hNX.1 (e (a - z)).
exists L; split=> //; split; first lra.
by split; first lra.
Qed.

Variable g : X -> X.
Variable s : R.
Hypothesis hs : 0 < s.
Hypothesis hs1 : s <= 1.
Hypothesis hg : is_smoothing_convolution hNX (fam s) e g.

(** Source for [dgpr_smoothing_value_bound]: the bound |e_eps(a)| <= c (|a| + 2)^c
    for 0 < eps <= 1, Federer 4.1.2, p. 347. *)
Lemma dgpr_smoothing_value_bound (a : X) : NX (g a) <= pw c (NX a + 1).
Proof.
have hy := @smoothing_convolution_alternate_integral R n X NX hNX (fam s) e g
  (@euclidean_own_norm_separable R n) hg a.
have h := @dgpr_kernel_mean_bound s (fun z => e (a - z)) (g a) 0 (pw c (NX a + 1)) hs hy.
rewrite subr0 in h; apply: h=> z hz; rewrite subr0.
by have [L [_ [h1 _]]] := dgpr_growth_ball a (ltW (lt_le_trans hz hs1)).
Qed.

(** Source for [dgpr_smoothing_distance]: the bound |e_eps(a) - e(a)| <= L eps,
    where L is a Lipschitz constant of e on B(a, 1), Federer 4.1.2,
    p. 347. *)
Lemma dgpr_smoothing_distance (a : X) (L : R) :
  (forall y w, NX (y - a) <= 1 -> NX (w - a) <= 1 -> NX (e y - e w) <= L * NX (y - w)) ->
  0 <= L -> NX (g a - e a) <= L * s.
Proof.
move=> hLip hL.
have hy := @smoothing_convolution_alternate_integral R n X NX hNX (fam s) e g
  (@euclidean_own_norm_separable R n) hg a.
apply: (@dgpr_kernel_mean_bound s (fun z => e (a - z)) (g a) (e a) (L * s) hs hy)=> z hz.
have hz1 : NX (a - z - a) <= 1.
  rewrite addrC addKr (real_seminorm_negate hNX.1); exact: ltW (lt_le_trans hz hs1).
have h0 : NX (a - a) <= 1 by rewrite subrr (real_seminorm_zero hNX.1).
apply: le_trans (hLip _ _ hz1 h0) _.
rewrite addrC addKr (real_seminorm_negate hNX.1).
by apply: ler_wpM2l=> //; exact: ltW.
Qed.

(** Source for [dgpr_smoothing_differential_bound]: the bound
    |De_eps(a)(v)| <= c (|a| + 2)^c |v| for 0 < eps <= 1, from the
    difference quotients of e_eps, Federer 4.1.2, p. 347. *)
Lemma dgpr_smoothing_differential_bound (a : X) (D : Hom X X) (v : X) :
  has_norm_differential NX NX setT g a D -> NX (D v) <= pw c (NX a + 1) * NX v.
Proof.
move=> hD.
have hl := norm_differential_directional_limit hNX hNX hD v.
have hv := real_seminorm_nonnegative hNX.1 v.
have hd : 0 < (NX v + 1)^-1 by rewrite invr_gt0; lra.
apply: (dgpr_punctured_limit_bound hl hd)=> t /andP [ht0 htd].
have hq := @smoothing_input_quotient_integral R n X NX hNX (@euclidean_own_norm_separable R n)
  e g (fam s) hg a v t.
have h := @dgpr_kernel_mean_bound s
  (fun z => t^-1 *: (e ((a - z) + t *: v) - e (a - z))) _ 0 (pw c (NX a + 1) * NX v) hs hq.
rewrite subr0 in h; apply: h=> z hz; rewrite subr0.
have [L [hL [_ [hLc hLip]]]] := dgpr_growth_ball a (ltW (lt_le_trans hz hs1)).
have hinv : (NX v + 1)^-1 * (NX v + 1) = 1 by rewrite mulVf // gt_eqF //; lra.
have hle := ltW htd.
have h0t : 0 <= `|t| := normr_ge0 t.
have htv : NX (t *: v) <= 1 by rewrite (real_seminorm_scale hNX.1); nra.
have h1 : NX ((a - z) + t *: v - (a - z)) <= 1 by rewrite addrC addKr.
have h2 : NX ((a - z) - (a - z)) <= 1 by rewrite subrr (real_seminorm_zero hNX.1).
have hE := hLip _ _ h1 h2.
have hdv : (a - z) + t *: v - (a - z) = t *: v by rewrite addrC addKr.
rewrite hdv (real_seminorm_scale hNX.1) in hE.
rewrite (real_seminorm_scale hNX.1) normfV.
have hti : 0 <= `|t|^-1 by rewrite invr_ge0.
apply: le_trans (ler_wpM2l hti hE) _.
rewrite [L * _]mulrCA mulKf; last exact: lt0r_neq0.
exact: (ler_wpM2r hv hLc).
Qed.

(** Source for [dgpr_iterated_two_arguments]: the arguments of D^2 for
    the iterated derivative D_v D_w, Federer 3.1.11, p. 223. *)
Lemma dgpr_iterated_two_arguments (v w : X) :
  iterated_directional_arguments [:: v; w] = args2 w v.
Proof. by rewrite /= multilinear_successor_zero_arguments. Qed.

(** Source for [dgpr_smoothing_second_bound]: for fixed eps, the bound
    |D^2 e_eps(a)(w, v)| <= C c (|a| + 2)^c |v| |w|, since
    D_v D_w e_eps = (D_v D_w Phi_eps) * e (Federer 4.1.2, p. 347) and the
    derivatives of Phi_eps are bounded (4.1.2, p. 346). *)
Lemma dgpr_smoothing_second_bound : exists C : R, 0 <= C /\
  forall (a : X) (z : ZX 2), dgpr_higher_differential hNX hNX setT g 2 a z ->
    forall v w, NX (evX 2 (args2 w v) z) <= C * pw c (NX a + 1) * (NX v * NX w).
Proof.
have hField := @continuous_field_locally_norm_integrable R n X NX hNX e dgpr_lipschitz_class_zero.
have hsm := @smoothing_dilation_smooth R n phi hPhi fam hFam s hs.
have hoff := @smoothing_dilation_zero_beyond_radius R n phi fam hPhi hFam s hs.
have [D0 [D [G [_ [_ [hD hG]]]]]] :=
  @smoothing_dilation_exact_derivative_norm R n phi hPhi fam hFam s 2 hs.
have hs2 : 0 < s ^+ 2 by rewrite exprn_gt0.
have [I hI] := dgpr_gaussian_summable n hs2.
pose M := G / (s ^+ (n + 2)).
have hM0 : 0 <= M := uniform_function_norm_nonnegative hG.
have hE1 := real_exponential_positive hE 1.
exists (M * E 1 * `|I|); split.
  by apply: mulr_ge0; [apply: mulr_ge0|]=> //; exact: ltW.
move=> a z hz v w.
have [theta [q [_ [htoff [hconv [htheta hq]]]]]] :=
  @compact_smooth_convolution_iterated_kernel R n X NX hNX (@euclidean_own_norm_complete R n)
    (@euclidean_own_norm_separable R n) e hField (fam s) hsm s hoff g hg [:: v; w].
have hthetaE x : theta x = evR 2 (args2 w v) (D x).
  have h := @norm_higher_differential_iterated_directions R X R^o NX NR hNX hNR
    (fun k => ZR k) (fun k => evR k) (fun k => ZNR k) (fun k => lawsR k) (fun _ => True)
    (fam s) [:: v; w] x (D x) (hD x).
  rewrite dgpr_iterated_two_arguments in h.
  exact: (norm_iterated_directional_unique hNR (htheta x) h).
have hqE : q a = evX 2 (args2 w v) z.
  have h := @norm_higher_differential_iterated_directions R X X NX NX hNX hNX
    (fun k => ZX k) (fun k => evX k) (fun k => ZNX k) (fun k => lawsX k) setT
    g [:: v; w] a z hz.
  rewrite dgpr_iterated_two_arguments in h.
  exact: (norm_iterated_directional_unique hNX (hq a) h).
have hN := real_seminorm_nonnegative hNX.1.
have hvw : 0 <= NX v * NX w by apply: mulr_ge0.
have hth x : `|theta x| <= M * (NX v * NX w).
  rewrite hthetaE; apply: le_trans (dgpr_second_bound (D x) v w) _.
  apply: ler_wpM2r=> //; apply: le_trans (ler_norm _) _.
  exact: (uniform_function_norm_bound hG x).
pose P := pw c (NX a + 1).
have hP : 0 <= P by apply: dgpr_polynomial_weight_nonnegative; exact: ltW.
pose K := M * (NX v * NX w) * P * E 1.
have hK : 0 <= K.
  by rewrite /K; apply: mulr_ge0; [apply: mulr_ge0; [apply: mulr_ge0|]|]=> //; exact: ltW.
have hIa : is_measure_integral mu (real_total_integrand
    (fun x => K * E (- NX (x - a) ^+ 2 / s ^+ 2))) (K * I)%:E.
  have h1 := dgpr_translation_integral (- a) hI.
  exact: (@real_total_integral_scale R X mu hm _ I K h1).
have hdom x : NX (theta (a - x) *: e x) <= K * E (- NX (x - a) ^+ 2 / s ^+ 2).
  rewrite (real_seminorm_scale hNX.1).
  have hEx := real_exponential_positive hE (- NX (x - a) ^+ 2 / s ^+ 2).
  case: (ltrP s (NX (a - x)))=> hx.
    by rewrite htoff // normr0 mul0r; apply: mulr_ge0=> //; exact: ltW.
  have hx1 : NX (a - x) <= 1 by apply: le_trans hx hs1.
  have [L [_ [he1 _]]] := dgpr_growth_ball a hx1.
  have hax : a - (a - x) = x by rewrite opprB addrCA subrr addr0.
  rewrite hax in he1.
  have hone : 1 <= E 1 * E (- NX (x - a) ^+ 2 / s ^+ 2).
    rewrite -(real_exponential_add hE) -(real_exponential_zero hE) real_exponential_order.
    have hxa : NX (x - a) <= s by rewrite (real_seminorm_subtract hNX.1).
    have hsq : NX (x - a) ^+ 2 <= s ^+ 2.
      by rewrite ler_sqr ?nnegrE //; exact: ltW.
    have : NX (x - a) ^+ 2 / s ^+ 2 <= 1 by rewrite ler_pdivrMr // mul1r.
    rewrite (real_exponential_zero hE) mulNr; lra.
  have hthx := hth (a - x).
  have h1 : `|theta (a - x)| * NX (e x) <= M * (NX v * NX w) * P.
    by apply: ler_pM=> //; exact: normr_ge0.
  apply: le_trans h1 _; rewrite /K.
  have hMP : 0 <= M * (NX v * NX w) * P by apply: mulr_ge0; [apply: mulr_ge0|].
  have h2 : M * (NX v * NX w) * P * 1 <=
      M * (NX v * NX w) * P * (E 1 * E (- NX (x - a) ^+ 2 / s ^+ 2)).
    exact: (ler_wpM2l hMP hone).
  by rewrite mulr1 mulrA in h2.
have hb' := @total_vector_integral_dominated_norm R X X NX hNX mu hm _ (q a) _ (K * I)
  (hconv a) hIa hdom.
rewrite -hqE; apply: le_trans hb' _.
have -> : M * E 1 * `|I| * pw c (NX a + 1) * (NX v * NX w) = K * `|I|.
  by rewrite /K /P; ring.
exact: (ler_wpM2l hK (ler_norm I)).
Qed.
End LipschitzSmoothing.

(** Source for [dgpr_differential_local]: the differential at a
    depends only on the values near a, Federer 3.1.1, p. 209. *)
Lemma dgpr_differential_local (R : realType) (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (f g : X -> Y) (a : X) (r : R) (L : Hom X Y) :
  0 < r -> (forall y, NX (y - a) < r -> f y = g y) ->
  has_norm_differential NX NY setT f a L -> has_norm_differential NX NY setT g a L.
Proof.
move=> hr hfg [hi hbd hrem]; split=> // eps heps.
have [d [hd hd']] := hrem eps heps.
exists (Num.min d r); split; first by rewrite lt_min hd hr.
move=> h _ hh.
have hhd : NX h < d by apply: lt_le_trans hh _; rewrite ge_min lexx.
have hhr : NX h < r by apply: lt_le_trans hh _; rewrite ge_min lexx orbT.
have h1 : f (a + h) = g (a + h) by apply: hfg; rewrite addrC addKr.
have h2 : f a = g a by apply: hfg; rewrite subrr (real_seminorm_zero hNX.1).
by rewrite -h1 -h2; exact: hd' h Logic.I hhd.
Qed.

Section Localisation.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T := (real_norm_metric_space hNX).
Local Notation IT := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Local Notation pw := dgpr_polynomial_weight.
Local Notation phi := (@regularising_kernel R n).
Local Notation fam := (@regularising_kernel_family R n).
Local Notation hPhi := (@regularising_kernel_laws R n).
Local Notation hFam := (@regularising_kernel_family_laws R n).

Variable e : X -> X.
Variable c : R.
Hypothesis hc : 0 < c.
Hypothesis hb : forall x, exists L, 0 <= L /\ NX (e x) + L <= pw c (NX x) /\
  forall y z, NX (y - x) <= 1 -> NX (z - x) <= 1 -> NX (e y - e z) <= L * NX (y - z).

(** Source for [dgpr_ball_extension]: for r > 0 there is a Lipschitzian
    map of R^n into R^n which agrees with e on B(0, r): e composed with
    a nonexpanding retraction of R^n onto B(0, r), since e is
    Lipschitzian on the compact set B(0, r) (Federer 2.2.7, p. 64). *)
Lemma dgpr_ball_extension (r : R) : 0 < r ->
  exists (f : X -> X) (M : R), 0 < M /\ (forall x, NX x <= r -> f x = e x) /\
    forall x y, NX (f x - f y) <= M * NX (x - y).
Proof.
move=> hr.
have [P [hrange [hfix hP]]] := @euclidean_closed_ball_retraction_exists R n (0 : IT) r (ltW hr).
have hK := @euclidean_norm_closed_ball_compact R n (0 : T) r.
have [M [hM [_ hMb]]] := @norm_local_lipschitz_compact R X X NX NX hNX hNX e _
  (dgpr_lipschitz_local hb) hK.
have hball x : NX x <= r -> metric_closed_ball (0 : T) r x.
  by move=> hx; rewrite /metric_closed_ball /= real_norm_metric_distanceE sub0r
    (real_seminorm_negate hNX.1).
have hPr x : NX (P x) <= r.
  have := hrange x.
  by rewrite /metric_closed_ball /= inner_metric_distanceE sub0r (real_seminorm_negate hNX.1).
exists (fun x => e (P x)), M; split=> //; split.
  by move=> x hx; rewrite hfix // /metric_closed_ball /= inner_metric_distanceE sub0r
    (real_seminorm_negate hNX.1).
move=> x y.
have h1 := hMb (P x) (P y) (hball _ (hPr x)) (hball _ (hPr y)).
rewrite !real_norm_metric_distanceE in h1.
apply: le_trans h1 _; apply: ler_wpM2l; first exact: ltW.
have [_ h2] := hP; have h3 := h2 x y Logic.I Logic.I.
by rewrite !inner_metric_distanceE mul1r in h3.
Qed.

(** Source for [dgpr_ball_index]: every point lies in some ball
    U(0, k + 1), k a natural number (archimedean property). *)
Lemma dgpr_ball_index (a : X) : exists k : nat, NX a < k.+1%:R.
Proof.
have h0 : 0 <= NX a := real_seminorm_nonnegative hNX.1 a.
exists (Num.bound (NX a)); apply: lt_le_trans (archi_boundP h0) _.
by rewrite ler_nat.
Qed.

(** Source for [dgpr_ball_inside]: the inequality |y| < r if
    |y - a| < r - |a|. *)
Lemma dgpr_ball_inside (a y : X) (r : R) : NX (y - a) < r - NX a -> NX y < r.
Proof.
move=> hy; have := real_seminorm_triangle hNX.1 a (y - a).
by rewrite addrC subrK; lra.
Qed.

(** Source for [dgpr_lipschitz_differentiable_ae]: lem:ibp, first
    assertion: a locally Lipschitzian e is differentiable at L^n almost
    all points, by Rademacher's theorem (Federer 3.1.6, pp. 216-217)
    applied to the
    Lipschitzian extensions of e from the balls B(0, k + 1). *)
Lemma dgpr_lipschitz_differentiable_ae :
  measure_almost_everywhere mu [set a | norm_differentiable_at NX NX setT e a].
Proof.
have hk (k : nat) : measure_almost_everywhere mu
    [set a | NX a < k.+1%:R -> norm_differentiable_at NX NX setT e a].
  have hr : (0 : R) < k.+1%:R by rewrite ltr0Sn.
  have [f [M [hM [hfe hLip]]]] := dgpr_ball_extension hr.
  have hLipI : is_metric_lipschitz setT (f : IT -> IT).
    exists M; split=> //; split; first exact: ltW.
    by move=> x y _ _; rewrite !inner_metric_distanceE; exact: hLip.
  have hD := @federer_3_1_6 R n n f hLipI.
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hD)=> a [L hL] ha.
  exists L; apply: (@dgpr_differential_local R X X NX NX hNX f e a (k.+1%:R - NX a) L _ _ hL).
    by rewrite subr_gt0.
  by move=> y hy; apply: hfe; apply: ltW; exact: dgpr_ball_inside hy.
have hall := @measure_almost_everywhere_countable R X nat mu hm setT _ (countableP setT)
  (fun k _ => hk k).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hall)=> a ha.
have [k hk'] := dgpr_ball_index a.
exact: (ha k Logic.I hk').
Qed.

(** Source for [dgpr_smoothing_differential_ae]: Federer 4.1.2, p. 347,
    with 2.9.9, pp. 156-157: for L^n almost all a, if e has the differential D at a,
    then De_eps(a)(v) -> D(v) as eps -> 0+. The globally Lipschitzian
    case (Federer 4.1.25, p. 383, supporting lemma) is applied to the
    extensions of e from the balls B(0, k + 1), whose smoothings agree
    with e_eps near a for small eps. *)
Lemma dgpr_smoothing_differential_ae (Es : R -> X -> X) (v : X) :
  (forall s, 0 < s -> is_smoothing_convolution hNX (fam s) e (Es s)) ->
  measure_almost_everywhere mu [set a | forall D, has_norm_differential NX NX setT e a D ->
    forall eta, 0 < eta -> exists d, 0 < d /\ forall s, 0 < s -> s < d ->
      forall D', has_norm_differential NX NX setT (Es s) a D' -> NX (D' v - D v) < eta].
Proof.
move=> hEs.
have hk (k : nat) : measure_almost_everywhere mu [set a | NX a < k.+1%:R ->
    forall D, has_norm_differential NX NX setT e a D ->
    forall eta, 0 < eta -> exists d, 0 < d /\ forall s, 0 < s -> s < d ->
      forall D', has_norm_differential NX NX setT (Es s) a D' -> NX (D' v - D v) < eta].
  have hr : (0 : R) < k.+1%:R by rewrite ltr0Sn.
  have [f [M [hM [hfe hLip]]]] := dgpr_ball_extension hr.
  have hlocf : is_locally_metric_lipschitz setT (f : T -> T).
    move=> x _; exists setT; split; first exact: filterT.
    exists M; split=> //; split; first exact: ltW.
    by move=> y z _ _; rewrite !real_norm_metric_distanceE; exact: hLip.
  have hfc := norm_continuous_whole_class_zero (metric_local_lipschitz_continuous_whole hlocf).
  have hField := @continuous_field_locally_norm_integrable R n X NX hNX f hfc.
  have hex s : exists G : X -> X, 0 < s -> is_smoothing_convolution hNX (fam s) f G.
    case: (pselect (0 < s))=> hs.
    - have [G hG] := @smoothing_convolution_exists R n X NX hNX
        (@euclidean_own_norm_complete R n) (@euclidean_own_norm_separable R n)
        phi hPhi fam hFam s hs f hField.
      by exists G.
    - by exists (fun _ => 0)=> hs'; contradiction.
  case: (choice hex)=> G hG.
  have hlib := @current_lipschitz_lebesgue_action_smoothing_direction_ae R n n f M (ltW hM)
    hLip phi hPhi fam hFam G hG v.
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hlib)=> a hA ha D hD eta heta.
  pose r := k.+1%:R - NX a.
  have hr0 : 0 < r by rewrite /r subr_gt0.
  have hDf : has_norm_differential NX NX setT f a D.
    apply: (@dgpr_differential_local R X X NX NX hNX e f a r D hr0 _ hD)=> y hy.
    by symmetry; apply: hfe; apply: ltW; exact: dgpr_ball_inside hy.
  have [d [hd hlim]] := hA D hDf eta heta.
  have hr2 : 0 < r / 2 by rewrite divr_gt0.
  exists (Num.min d (r / 2)); split; first by rewrite lt_min hd hr2.
  move=> s hs hsd D' hD'.
  have hsd1 : s < d by apply: lt_le_trans hsd _; rewrite ge_min lexx.
  have hsr : s < r / 2 by apply: lt_le_trans hsd _; rewrite ge_min lexx orbT.
  have hloc y : NX (y - a) < r / 2 -> Es s y = G s y.
    move=> hy; apply: (measure_vector_integral_unique (hEs s hs y)).
    have -> : (fun z => (fam s (y - z) *: e z : T)) = (fun z => (fam s (y - z) *: f z : T)).
      apply: funext=> z; case: (eqVneq (fam s (y - z)) 0)=> hz.
        by rewrite hz !scale0r.
      have hyz := @smoothing_dilation_nonzero_radius R n phi fam hPhi hFam s hs (y - z) hz.
      rewrite hfe //; apply: ltW; apply: (@dgpr_ball_inside a z).
      have h1 := real_seminorm_triangle hNX.1 (y - a) (z - y).
      have h2 : y - a + (z - y) = z - a by rewrite addrC addrA subrK.
      rewrite h2 (real_seminorm_subtract hNX.1 z y) in h1.
      rewrite -/r; lra.
    exact: (hG s hs y).
  have hD'G := @dgpr_differential_local R X X NX NX hNX (Es s) (G s) a (r / 2) D' hr2 hloc hD'.
  have hcm := @current_map_differential_unique R n n setT (G s) a D' hD'G.
  by rewrite -hcm; exact: hlim s hs hsd1.
have hall := @measure_almost_everywhere_countable R X nat mu hm setT _ (countableP setT)
  (fun k _ => hk k).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hall)=> a ha.
have [k hk'] := dgpr_ball_index a.
exact: (ha k Logic.I hk').
Qed.
End Localisation.
