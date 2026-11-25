(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3, the heat
    kernel; blueprint dgpr_blueprint.tex, def:heat and lem:kernel(1),(2),(6).
    For 0 < s < oo and z in R^n the heat kernel is
    p_s(z) = (4 pi s)^(-n/2) exp(-|z|^2/(4s)); here (4 pi s)^(-n/2) is written
    (Num.sqrt (4 pi s))^-n, and pi, exp and the Lebesgue measure L^n are those
    of Federer's library. The Gaussian integrals are derived from Federer
    3.2.13, p. 250 (the Gamma product integral), and Gamma(1/2)^2 = pi from
    the volume alpha(2) = pi of the unit disc. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  CircularTrigonometrySealed CircularUnitCircleLength RealPower RealPowerNaturalHausdorff
  RealExponentialUP RealExponentialSealed EuclideanBallVolume UnitBallGammaVolume
  EulerGamma EulerGammaOne EulerGammaRecurrence EulerGammaHalfParameters GammaGaussianProductIntegral
  GaussianProductIntegrand SphereGammaMass EuclideanDilationPushforward MeasureScaleIntegral
  InjectivePushforwardIntegral CovariantMeasureImage MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  SummableRealFunctionUP SummableRealArithmetic LatticeL1ApproximationLaws EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [dgpr_pi]: the number pi of DPGPR 2026, section 3 (blueprint
    def:heat), taken as the half period of Federer's circular functions. *)
Definition dgpr_pi (R : realType) : R := CircularTrigonometry.half_period R.

Section HeatKernel.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation exp := (@RealExponential.exponential R).
Local Notation LL := (@euclidean_lebesgue_measure R n).

(** Source for [dgpr_heat_kernel]: DPGPR 2026, section 3, p_s(z) =
    (4 pi s)^(-n/2) exp(-|z|^2/(4s)) (blueprint def:heat); the factor
    (4 pi s)^(-n/2) is written (Num.sqrt (4 pi s))^-n. The formula is
    meaningful for 0 < s. *)
Definition dgpr_heat_kernel (s : R) (z : X) : R :=
  (Num.sqrt (4 * dgpr_pi R * s)) ^- n * exp (- N z ^+ 2 / (4 * s)).

(** Source for [dgpr_gamma_half_sqr]: Gamma(1/2)^2 = pi, from
    alpha(2) = Gamma(1/2)^2 / Gamma(2) (Federer 3.2.13, p. 251) and alpha(2) = pi;
    used in blueprint lem:kernel(1). *)
Lemma dgpr_gamma_half_sqr : euler_gamma_half R ^+ 2 = dgpr_pi R.
Proof.
have h := @euclidean_unit_ball_gamma_volume R 2 isT.
rewrite circular_half_period_planar_volume in h.
have hg2 (t : R) (ht : 0 < t) : t = 1 + 1 -> euler_gamma ht = 1.
  move=> et; subst t.
  have h1 : (0 : R) < 1 := ltr01.
  by rewrite (euler_gamma_recurrence h1 ht) mul1r euler_gamma_one.
rewrite hg2 ?divr1 in h; first by rewrite /dgpr_pi h.
by rewrite divff // pnatr_eq0.
Qed.

(** Source for [dgpr_pi_gt0]: positivity of pi, used throughout blueprint
    lem:kernel. *)
Lemma dgpr_pi_gt0 : 0 < dgpr_pi R.
Proof. by rewrite -dgpr_gamma_half_sqr exprn_gt0 // euler_gamma_positive. Qed.

(** Source for [dgpr_gamma_half_sqrt]: Gamma(1/2) = pi^(1/2); blueprint
    lem:kernel(1). *)
Lemma dgpr_gamma_half_sqrt : euler_gamma_half R = Num.sqrt (dgpr_pi R).
Proof.
by rewrite -dgpr_gamma_half_sqr sqrtr_sqr gtr0_norm // euler_gamma_positive.
Qed.

(** Source for [dgpr_gamma_at_half]: Gamma(t) = pi^(1/2) for t = 1/2,
    for every proof of 0 < t; blueprint lem:kernel(1). *)
Lemma dgpr_gamma_at_half (t : R) (ht : 0 < t) : t = 1 / 2 -> euler_gamma ht = Num.sqrt (dgpr_pi R).
Proof.
move=> et; subst t; rewrite -dgpr_gamma_half_sqrt /euler_gamma_half.
exact: euler_gamma_proof_irrelevant.
Qed.

(** Source for [dgpr_gamma_at_three_halves]: Gamma(3/2) = 2^(-1) pi^(1/2),
    by Gamma(t+1) = t Gamma(t) (Federer 3.2.13); blueprint lem:kernel(2). *)
Lemma dgpr_gamma_at_three_halves (t : R) (ht : 0 < t) :
  t = 3 / 2 -> euler_gamma ht = 1 / 2 * Num.sqrt (dgpr_pi R).
Proof.
move=> et; have et' : t = 1 / 2 + 1 by rewrite et; lra.
clear et; subst t; rewrite (euler_gamma_recurrence (positive_real_half R) ht).
by rewrite -/(euler_gamma_half R) dgpr_gamma_half_sqrt.
Qed.

(** Source for [dgpr_gaussian_integral]: the integral of
    [x |-> exp(-|x|^2)] with respect to L^n equals pi^(n/2), the case
    z_j = 1/2 of Federer 3.2.13, p. 250; blueprint lem:kernel(1). *)
Lemma dgpr_gaussian_integral :
  is_measure_integral LL (real_total_integrand (fun x : X => exp (- N x ^+ 2)))
    (Num.sqrt (dgpr_pi R) ^+ n)%:E.
Proof.
have h := @gamma_gaussian_product_integral R n (fun _ => 1 / 2) (fun _ => positive_real_half R).
have e1 : \prod_(j < n) euler_gamma (positive_real_half R) = Num.sqrt (dgpr_pi R) ^+ n.
  rewrite (eq_bigr (fun _ => Num.sqrt (dgpr_pi R))); first by rewrite prodr_const card_ord.
  by move=> j _; exact: dgpr_gamma_at_half.
rewrite e1 in h.
have e2 : gaussian_product_integrand (fun _ : 'I_n => 1 / 2 : R) = (fun x : X => exp (- N x ^+ 2)).
  by apply: funext => x; rewrite /gaussian_product_integrand gaussian_half_angular_constant mulr1.
by rewrite e2 in h.
Qed.

(** Source for [dgpr_lebesgue_dilation]: for 0 < e, the integral of
    [x |-> g(e^(-1) x)] with respect to L^n equals e^n times that of g
    (Federer 2.4.18 and 2.10.35 through the dilation pushforward of L^n);
    blueprint lem:kernel(1),(2). *)
Lemma dgpr_lebesgue_dilation (g : X -> R) (e a : R) : 0 < e ->
  is_measure_integral LL (real_total_integrand g) a%:E ->
  is_measure_integral LL (real_total_integrand (fun x : X => g (e^-1 *: x))) (e ^+ n * a)%:E.
Proof.
move=> he hg.
have hm := euclidean_lebesgue_is_measure R n.
have h1 := measure_scale_integral hm (exprn_gt0 n he) hg.
have h1' : is_measure_integral (MeasurePushforward.measure_pushforward (fun x : X => e^-1 *: x) LL)
    (real_total_integrand g) (e ^+ n * a)%:E.
  by rewrite (euclidean_inverse_dilation_pushforward n he) EFinM.
have hinj : injective (fun x : X => e^-1 *: x).
  by apply: scalerI; rewrite invr_eq0 gt_eqF.
have h2 := (@injective_pushforward_integral_iff R _ _ LL hm (fun x : X => e^-1 *: x)
  (real_total_integrand g) hinj _).2 h1'.
exact: (measure_integral_graph_equivalent
  (fun x y => precompose_total_integrand_graph (fun x : X => e^-1 *: x) g x y) h2).
Qed.


(** Source for [dgpr_real_integral_sum]: additivity of the integral over
    finite sums of summable real functions (Federer 2.4.4(4)); blueprint
    lem:kernel(2). *)
Lemma dgpr_real_integral_sum (Y : choiceType) (mu : set Y -> \bar R) (J : finType)
    (f : J -> Y -> R) (a : J -> R) :
  MeasureUP.is_measure mu ->
  (forall j, is_measure_integral mu (real_total_integrand (f j)) (a j)%:E) ->
  is_measure_integral mu (real_total_integrand (fun y => \sum_j f j y)) (\sum_j a j)%:E.
Proof.
move=> hm hf.
suff h : forall r : seq J, is_measure_integral mu
    (real_total_integrand (fun y => \sum_(j <- r) f j y)) (\sum_(j <- r) a j)%:E.
  exact: h.
elim=> [|j r ih].
  have -> : (fun y => \sum_(j <- [::]) f j y) = (fun _ => 0) by apply: funext => y; rewrite big_nil.
  rewrite big_nil; exact: real_total_zero_integral hm.
have -> : (fun y => \sum_(i <- j :: r) f i y) = (fun y => f j y + \sum_(i <- r) f i y).
  by apply: funext => y; rewrite big_cons.
rewrite big_cons; exact: (@real_total_integral_add R Y mu hm (f j)
  (fun y => \sum_(i <- r) f i y) (a j) (\sum_(i <- r) a i) (hf j) ih).
Qed.

(** Source for [dgpr_dilated_norm_sqr]: |(4s)^(-1/2) z|^2 = |z|^2/(4s) for
    0 < s; blueprint lem:kernel(1),(2). *)
Lemma dgpr_dilated_norm_sqr (s : R) (z : X) : 0 < s ->
  N ((Num.sqrt (4 * s))^-1 *: z) ^+ 2 = N z ^+ 2 / (4 * s).
Proof.
move=> hs; have h4 : 0 < 4 * s by rewrite mulr_gt0.
rewrite inner_normZ exprMn gtr0_norm ?invr_gt0 ?sqrtr_gt0 // exprVn sqr_sqrtr ?ltW //.
by rewrite mulrC.
Qed.

(** Source for [dgpr_normaliser]: (4 pi s)^(-n/2) (4s)^(n/2) pi^(n/2) = 1
    for 0 < s; blueprint lem:kernel(1),(2). *)
Lemma dgpr_normaliser (s : R) : 0 < s ->
  (Num.sqrt (4 * dgpr_pi R * s)) ^- n * (Num.sqrt (4 * s) ^+ n * Num.sqrt (dgpr_pi R) ^+ n) = 1.
Proof.
move=> hs; have h4 : 0 <= 4 * s by rewrite ltW // mulr_gt0.
have e : 4 * s * dgpr_pi R = 4 * dgpr_pi R * s by rewrite mulrAC.
have hp : 0 < Num.sqrt (4 * dgpr_pi R * s).
  by rewrite sqrtr_gt0 mulr_gt0 // mulr_gt0 // dgpr_pi_gt0.
by rewrite -exprMn -sqrtrM // e mulVf // expf_neq0 // gt_eqF.
Qed.

(** Source for [dgpr_kernel_mass]: DPGPR 2026, section 3; blueprint
    lem:kernel(1), the integral of p_s with respect to L^n equals 1 for 0 < s. *)
Lemma dgpr_kernel_mass (s : R) : 0 < s ->
  is_measure_integral LL (real_total_integrand (dgpr_heat_kernel s)) 1%:E.
Proof.
move=> hs; have hm := euclidean_lebesgue_is_measure R n.
have he : 0 < Num.sqrt (4 * s) by rewrite sqrtr_gt0 mulr_gt0.
have h := dgpr_lebesgue_dilation he dgpr_gaussian_integral.
have h2 := real_total_integral_scale hm ((Num.sqrt (4 * dgpr_pi R * s)) ^- n) h.
rewrite dgpr_normaliser // in h2.
have -> : dgpr_heat_kernel s = (fun x : X => (Num.sqrt (4 * dgpr_pi R * s)) ^- n *
    exp (- N ((Num.sqrt (4 * s))^-1 *: x) ^+ 2)).
  by apply: funext => x; rewrite /dgpr_heat_kernel dgpr_dilated_norm_sqr // mulNr.
exact: h2.
Qed.

(** Source for [dgpr_gaussian_coordinate_integral]: the integral of
    [x |-> x_i^2 exp(-|x|^2)] with respect to L^n equals 2^(-1) pi^(n/2), the case
    z_i = 3/2 and z_j = 1/2 for j != i of Federer 3.2.13, p. 250;
    blueprint lem:kernel(2). *)
Lemma dgpr_gaussian_coordinate_integral (i : 'I_n) :
  is_measure_integral LL (real_total_integrand (fun x : X => x i ^+ 2 * exp (- N x ^+ 2)))
    (1 / 2 * Num.sqrt (dgpr_pi R) ^+ n)%:E.
Proof.
pose z := fun j : 'I_n => if j == i then 3 / 2 else 1 / 2 : R.
have hz j : 0 < z j by rewrite /z; case: (j == i); lra.
have h := @gamma_gaussian_product_integral R n z hz.
have e1 : \prod_j euler_gamma (hz j) = 1 / 2 * Num.sqrt (dgpr_pi R) ^+ n.
  rewrite (eq_bigr (fun j => (if j == i then 1 / 2 else 1) * Num.sqrt (dgpr_pi R))).
    by rewrite big_split /= -big_mkcond big_pred1_eq prodr_const card_ord.
  move=> j _; case: (boolP (j == i)) => hji.
    have hzj : z j = 3 / 2 by rewrite /z hji.
    by rewrite (dgpr_gamma_at_three_halves (hz j) hzj).
  have hzj : z j = 1 / 2 by rewrite /z (negbTE hji).
  by rewrite (dgpr_gamma_at_half (hz j) hzj) /= mul1r.
rewrite e1 in h.
have e2 : gaussian_product_integrand z = (fun x : X => x i ^+ 2 * exp (- N x ^+ 2)).
  apply: funext => x; rewrite /gaussian_product_integrand mulrC; congr (_ * _).
  rewrite /gaussian_angular_integrand (bigD1 i) //= big1 ?mulr1.
    have -> : 2 * z i - 1 = 2%:R by rewrite /z eqxx; lra.
    by rewrite real_power_natural_exponent ?normr_ge0 // real_normK // num_real.
  move=> j hji; have -> : 2 * z j - 1 = 0 by rewrite /z (negbTE hji); lra.
  exact: real_power_zero_exponent.
by rewrite e2 in h.
Qed.

(** Source for [dgpr_gaussian_moment]: the integral of
    [x |-> |x|^2 exp(-|x|^2)] with respect to L^n equals (n/2) pi^(n/2);
    blueprint lem:kernel(2). *)
Lemma dgpr_gaussian_moment :
  is_measure_integral LL (real_total_integrand (fun x : X => N x ^+ 2 * exp (- N x ^+ 2)))
    (n%:R / 2 * Num.sqrt (dgpr_pi R) ^+ n)%:E.
Proof.
have hm := euclidean_lebesgue_is_measure R n.
have h := dgpr_real_integral_sum hm dgpr_gaussian_coordinate_integral.
have -> : (fun x : X => N x ^+ 2 * exp (- N x ^+ 2)) =
    (fun x : X => \sum_(i < n) x i ^+ 2 * exp (- N x ^+ 2)).
  apply: funext => x; rewrite -mulr_suml; congr (_ * _).
  by rewrite inner_norm_sqr /euclidean_inner_product; apply: eq_bigr => j _; rewrite expr2.
have -> : n%:R / 2 * Num.sqrt (dgpr_pi R) ^+ n = \sum_(i < n) (1 / 2 * Num.sqrt (dgpr_pi R) ^+ n).
  by rewrite sumr_const card_ord -[in RHS]mulr_natl; field.
exact: h.
Qed.

(** Source for [dgpr_kernel_moment]: DPGPR 2026, section 3; blueprint
    lem:kernel(2), the integral of [z |-> |z|^2 p_s(z)] with respect to L^n
    equals 2 n s for 0 < s. *)
Lemma dgpr_kernel_moment (s : R) : 0 < s ->
  is_measure_integral LL (real_total_integrand (fun z : X => N z ^+ 2 * dgpr_heat_kernel s z))
    (2 * n%:R * s)%:E.
Proof.
move=> hs; have hm := euclidean_lebesgue_is_measure R n.
have he : 0 < Num.sqrt (4 * s) by rewrite sqrtr_gt0 mulr_gt0.
have h := dgpr_lebesgue_dilation he dgpr_gaussian_moment.
have h2 := real_total_integral_scale hm ((Num.sqrt (4 * dgpr_pi R * s)) ^- n * (4 * s)) h.
have hc := dgpr_normaliser hs.
have -> : 2 * n%:R * s = (Num.sqrt (4 * dgpr_pi R * s)) ^- n * (4 * s) *
    (Num.sqrt (4 * s) ^+ n * (n%:R / 2 * Num.sqrt (dgpr_pi R) ^+ n)).
  move: hc; move: (Num.sqrt (4 * dgpr_pi R * s) ^- n) (Num.sqrt (4 * s) ^+ n)
    (Num.sqrt (dgpr_pi R) ^+ n) => c E P hc.
  have -> : c * (4 * s) * (E * (n%:R / 2 * P)) = c * (E * P) * (2 * n%:R * s) by field.
  by rewrite hc mul1r.
have -> : (fun z : X => N z ^+ 2 * dgpr_heat_kernel s z) = (fun z : X =>
    (Num.sqrt (4 * dgpr_pi R * s)) ^- n * (4 * s) *
    (N ((Num.sqrt (4 * s))^-1 *: z) ^+ 2 * exp (- N ((Num.sqrt (4 * s))^-1 *: z) ^+ 2))).
  apply: funext => z; rewrite dgpr_dilated_norm_sqr // /dgpr_heat_kernel (mulNr (N z ^+ 2)).
  move: (Num.sqrt (4 * dgpr_pi R * s) ^- n) (exp (- (N z ^+ 2 / (4 * s)))) => c E.
  by field; rewrite lt0r_neq0.
exact: h2.
Qed.

(** Source for [dgpr_exponential_le]: monotonicity of the exponential;
    blueprint lem:kernel(6). *)
Lemma dgpr_exponential_le (a b : R) : a <= b -> exp a <= exp b.
Proof.
rewrite le_eqVlt => /orP [/eqP -> //|hab].
by apply: ltW; rewrite (real_exponential_strict_order (@RealExponential.laws R)).
Qed.

(** Source for [dgpr_kernel_gt0]: p_s(z) > 0 for 0 < s; blueprint def:heat
    and lem:semiconvex. *)
Lemma dgpr_kernel_gt0 (s : R) (z : X) : 0 < s -> 0 < dgpr_heat_kernel s z.
Proof.
move=> hs; rewrite /dgpr_heat_kernel; apply: mulr_gt0.
  by rewrite invr_gt0 exprn_gt0 // sqrtr_gt0 mulr_gt0 // mulr_gt0 // dgpr_pi_gt0.
exact: (real_exponential_positive (@RealExponential.laws R) _).
Qed.

(** Source for [dgpr_kernel_max]: DPGPR 2026, section 3; blueprint
    lem:kernel(6), p_s(z) <= (4 pi s)^(-n/2) for 0 < s. *)
Lemma dgpr_kernel_max (s : R) (z : X) : 0 < s ->
  dgpr_heat_kernel s z <= (Num.sqrt (4 * dgpr_pi R * s)) ^- n.
Proof.
move=> hs; rewrite /dgpr_heat_kernel -[X in _ <= X]mulr1 ler_wpM2l //.
  by rewrite invr_ge0 exprn_ge0 // sqrtr_ge0.
have e0 : exp 0 = 1 := real_exponential_zero (@RealExponential.laws R).
rewrite -[X in _ <= X]e0; apply: dgpr_exponential_le.
rewrite (mulNr (N z ^+ 2)) oppr_le0; apply: divr_ge0; first exact: sqr_ge0.
by apply: ltW; rewrite mulr_gt0.
Qed.

End HeatKernel.
