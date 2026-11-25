(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3, the
    derivatives of the heat kernel; blueprint dgpr_blueprint.tex,
    lem:kernel(3),(5). The differentials are those of Federer 3.1.1 on the
    Euclidean space R^n with values in R; the second differential
    D^2 p_s(z)(v,w) is the differential at z of [x |-> D p_s(x)(v)] applied
    to w. The time derivative is computed on the domain {t : 0 < t}. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerNormInequalities RealExponentialUP RealExponentialSealed RealExponentialDifferential TensorUP
  NormDifferentialUP NormDifferentialLinear NormDifferentialArithmetic NormDifferentialChain
  NormDifferentialBilinearProduct NormBilinearDifferentialAlgebra NormHigherCurveDerivativeUP
  ScalarCoefficientLinearAlgebra ScalarPowerDifferential ScalarSquareRootDifferential
  ScalarReciprocalDifferential ScalarHornerDifferential NormDifferentialScalar NormedCurveDerivativeUP
  FiniteCoordinates CoordinateProjection EuclideanCoordinateMetric CircularTrigonometrySealed.
From DPGPR Require Import DgprHeatKernel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section HeatKernelDifferential.
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

(** Source for [dgpr_inner_linear]: linearity of [v |-> z . v]
    (Federer 1.7.1); blueprint lem:kernel(5). *)
Lemma dgpr_inner_linear (z : X) : linear (fun v : X => (B z v : R^o)).
Proof. exact: (@euclidean_inner_bilinear R n).2 z. Qed.

(** Source for [dgpr_inner_hom]: the linear map [v |-> z . v] in
    Hom(R^n, R); blueprint lem:kernel(5). *)
Definition dgpr_inner_hom (z : X) : Hom X R^o :=
  @HomMap R X R^o (fun v => B z v) (asboolT (dgpr_inner_linear z)).

(** Source for [dgpr_inner_homE]: evaluation of [dgpr_inner_hom];
    blueprint lem:kernel(5). *)
Lemma dgpr_inner_homE (z v : X) : dgpr_inner_hom z v = B z v.
Proof. by []. Qed.

(** Source for [dgpr_inner_hom_bounded]: |z . v| <= |z| |v| (Federer
    1.7.1); blueprint lem:kernel(5). *)
Lemma dgpr_inner_hom_bounded (z : X) : norm_bounded_linear N A1 (dgpr_inner_hom z).
Proof.
exists (N z); split; first exact: inner_norm_nonnegative.
move=> h; exact: (inner_cauchy (@euclidean_inner_productP R n) z h).
Qed.

(** Source for [dgpr_interior_setT]: every point is interior to R^n;
    blueprint lem:kernel(5). *)
Lemma dgpr_interior_setT (a : X) : norm_domain_interior N setT a.
Proof. by exists 1; split => //; exact: ltr01. Qed.

(** Source for [dgpr_identity_linear]: linearity of the identity map of
    R^n; blueprint lem:kernel(5). *)
Lemma dgpr_identity_linear : linear (fun x : X => x).
Proof. by []. Qed.

(** Source for [dgpr_identity_hom]: the identity map of R^n as an element
    of Hom(R^n, R^n); blueprint lem:kernel(5). *)
Definition dgpr_identity_hom : Hom X X :=
  @HomMap R X X (fun x => x) (asboolT dgpr_identity_linear).

(** Source for [dgpr_mul_bilinear]: bilinearity of the multiplication of
    R, used in the product rule of Federer 3.1.11; blueprint lem:kernel(5). *)
Lemma dgpr_mul_bilinear : @TensorUP.bilinear R R^o R^o R^o (fun u w : R^o => (u * w : R^o)).
Proof.
split=> [w|u] a x y.
  by change ((a * x + y) * w = a * (x * w) + y * w); ring.
by change (u * (a * x + y) = a * (u * x) + u * y); ring.
Qed.

(** Source for [dgpr_kernel_differential]: the linear map
    [v |-> -(2s)^(-1) (z . v) p_s(z)] of DPGPR 2026, section 3 (blueprint
    lem:kernel(5), first formula). *)
Definition dgpr_kernel_differential (s : R) (z : X) : Hom X R^o :=
  (- (2 * s)^-1 * p s z) *: dgpr_inner_hom z.

(** Source for [dgpr_kernel_differentialE]: evaluation of
    [dgpr_kernel_differential]; blueprint lem:kernel(5). *)
Lemma dgpr_kernel_differentialE (s : R) (z v : X) :
  dgpr_kernel_differential s z v = - (2 * s)^-1 * B z v * p s z.
Proof.
by change (- (2 * s)^-1 * p s z * B z v = - (2 * s)^-1 * B z v * p s z); rewrite mulrAC.
Qed.

(** Source for [dgpr_kernel_exponent]: -|z|^2/(4s) = -(4s)^(-1) (z . z);
    blueprint lem:kernel(5). *)
Lemma dgpr_kernel_exponent (s : R) (z : X) :
  - N z ^+ 2 / (4 * s) = - (4 * s)^-1 * B z z.
Proof. by rewrite inner_norm_sqr mulNr mulrC mulNr. Qed.

(** Source for [dgpr_kernel_differential_formula]: DPGPR 2026, section 3;
    blueprint lem:kernel(5), D p_s(z)(v) = -(2s)^(-1) (z . v) p_s(z) for
    0 < s, as a differential in the sense of Federer 3.1.1. *)
Theorem dgpr_kernel_differential_formula (s : R) (z : X) : 0 < s ->
  has_norm_differential N A1 setT (p s) z (dgpr_kernel_differential s z).
Proof.
move=> hs.
pose c := (Num.sqrt (4 * dgpr_pi R * s)) ^- n.
pose k := - (4 * s)^-1.
have hI : has_norm_differential N N setT dgpr_identity_hom z dgpr_identity_hom.
  apply: (norm_differential_linear hN hN (dgpr_interior_setT z)).
  by exists 1; split => // h; rewrite mul1r.
have hB u v : `|B u v| <= 1 * (N u * N v).
  by rewrite mul1r; exact: (inner_cauchy (@euclidean_inner_productP R n) u v).
have hQ0 := norm_differential_bilinear_product hN hN hN hA (@euclidean_inner_bilinear R n)
  (@ler01 R) hB hI hI.
have hQ : has_norm_differential N A1 setT (fun x : X => (B x x : R^o)) z
    (norm_bilinear_product_linear_term (@euclidean_inner_bilinear R n) z z dgpr_identity_hom
    dgpr_identity_hom) := hQ0.
have hq := norm_differential_scale hN hA k hQ.
have hE := @real_exponential_differential R (k *: (B z z : R^o)).
have hC := norm_differential_chain hN hA hA hq hE.
have hP := norm_differential_scale hN hA c hC.
have eA : (fun x : X => setT x /\ True) = setT.
  by apply: funext => x; apply: propext; split.
have ef : (fun x : X => c *: (exp (k *: (B x x : R^o)) : R^o)) = p s.
  apply: funext => x; rewrite /dgpr_heat_kernel dgpr_kernel_exponent.
  by [].
rewrite eA ef in hP.
have eL : c *: hom_comp (real_exponential_linear_term (k *: (B z z : R^o))) (k *:
    norm_bilinear_product_linear_term (@euclidean_inner_bilinear R n) z z dgpr_identity_hom
    dgpr_identity_hom) = dgpr_kernel_differential s z.
  apply: hom_ext => v; rewrite dgpr_kernel_differentialE.
  change (c * (exp (k * B z z) * (k * (B v z + B z v))) = - (2 * s)^-1 * B z v * p s z).
  rewrite /dgpr_heat_kernel dgpr_kernel_exponent -/c -/k (euclidean_inner_symmetric v z).
  move: (exp (k * B z z)) => E; rewrite /k.
  by field; rewrite lt0r_neq0.
by rewrite eL in hP.
Qed.


(** Source for [dgpr_kernel_second]: the linear map
    [w |-> ((4s^2)^(-1) (z . v)(z . w) - (2s)^(-1) v . w) p_s(z)];
    blueprint lem:kernel(5), second formula. *)
Definition dgpr_kernel_second (s : R) (z v : X) : Hom X R^o :=
  ((4 * s ^+ 2)^-1 * B z v * p s z) *: dgpr_inner_hom z - ((2 * s)^-1 * p s z) *: dgpr_inner_hom v.

(** Source for [dgpr_kernel_secondE]: evaluation of [dgpr_kernel_second];
    blueprint lem:kernel(5). *)
Lemma dgpr_kernel_secondE (s : R) (z v w : X) :
  dgpr_kernel_second s z v w = ((4 * s ^+ 2)^-1 * B z v * B z w - (2 * s)^-1 * B v w) * p s z.
Proof.
change ((4 * s ^+ 2)^-1 * B z v * p s z * B z w - (2 * s)^-1 * p s z * B v w =
  ((4 * s ^+ 2)^-1 * B z v * B z w - (2 * s)^-1 * B v w) * p s z).
by ring.
Qed.

(** Source for [dgpr_kernel_second_formula]: DPGPR 2026, section 3;
    blueprint lem:kernel(5), D^2 p_s(z)(v,w) = ((4s^2)^(-1) (z . v)(z . w) -
    (2s)^(-1) v . w) p_s(z), as the differential at z of [x |-> D p_s(x)(v)]. *)
Theorem dgpr_kernel_second_formula (s : R) (z v : X) : 0 < s ->
  has_norm_differential N A1 setT (fun x : X => dgpr_kernel_differential s x v) z
    (dgpr_kernel_second s z v).
Proof.
move=> hs.
pose F1 : Hom X R^o := (- (2 * s)^-1) *: dgpr_inner_hom v.
have hF1 : has_norm_differential N A1 setT F1 z F1.
  apply: (norm_differential_linear hN hA (dgpr_interior_setT z)).
  by apply: norm_bounded_linear_scale; [exact: hA | exact: dgpr_inner_hom_bounded].
have hP := dgpr_kernel_differential_formula z hs.
have hM u w : A1 (u * w : R^o) <= 1 * (A1 u * A1 w) by rewrite mul1r normrM.
have hD := norm_differential_bilinear_product hN hA hA hA dgpr_mul_bilinear (@ler01 R) hM hF1 hP.
have ef : (fun x : X => (F1 x * p s x : R^o)) = (fun x : X => dgpr_kernel_differential s x v).
  apply: funext => x; rewrite dgpr_kernel_differentialE.
  change (- (2 * s)^-1 * B v x * p s x = - (2 * s)^-1 * B x v * p s x).
  by rewrite (euclidean_inner_symmetric v x).
have eL : norm_bilinear_product_linear_term dgpr_mul_bilinear (F1 z) (p s z) F1
    (dgpr_kernel_differential s z) = dgpr_kernel_second s z v.
  apply: hom_ext => w; rewrite dgpr_kernel_secondE.
  change (- (2 * s)^-1 * B v w * p s z + - (2 * s)^-1 * B v z * dgpr_kernel_differential s z w =
    ((4 * s ^+ 2)^-1 * B z v * B z w - (2 * s)^-1 * B v w) * p s z).
  rewrite dgpr_kernel_differentialE (euclidean_inner_symmetric v z).
  by field; rewrite lt0r_neq0.
have hD' : has_norm_differential N A1 setT (fun x : X => (F1 x * p s x : R^o)) z
    (norm_bilinear_product_linear_term dgpr_mul_bilinear (F1 z) (p s z) F1
    (dgpr_kernel_differential s z)) := hD.
by rewrite ef eL in hD'.
Qed.


(** Source for [dgpr_scm_scale]: c (t |-> t l) = (t |-> t (c l)) in
    Hom(R, R); blueprint lem:kernel(3). *)
Lemma dgpr_scm_scale (c l : R) :
  c *: @scalar_coefficient_linear_map R R^o l = scalar_coefficient_linear_map (c * l : R^o).
Proof. by apply: hom_ext => t; change (c * (t * l) = t * (c * l)); ring. Qed.

(** Source for [dgpr_exponential_term]: the differential of exp at e is
    multiplication by exp(e); blueprint lem:kernel(3). *)
Lemma dgpr_exponential_term (e : R) :
  real_exponential_linear_term e = @scalar_coefficient_linear_map R R^o (exp e).
Proof. by apply: hom_ext => t; change (exp e * t = t * exp e); rewrite mulrC. Qed.

(** Source for [dgpr_positive_interior]: every positive number is interior
    to {t : 0 < t}; blueprint lem:kernel(3). *)
Lemma dgpr_positive_interior (a : R) : 0 < a -> norm_domain_interior A1 (fun t : R => 0 < t) a.
Proof.
move=> ha; exists a; split => // h hh /=.
by move: hh; rewrite ltr_norml => /andP [h1 _]; lra.
Qed.

(** Source for [dgpr_time_algebra]: the algebraic identity behind
    d/ds p_s(z) = ((4s^2)^(-1) |z|^2 - n (2s)^(-1)) p_s(z); blueprint
    lem:kernel(3). *)
Lemma dgpr_time_algebra (s q a E r P : R) (m : nat) :
  s != 0 -> r != 0 -> P != 0 -> r ^+ 2 = 4 * q * s -> m%:R * r ^+ m.-1 = m%:R * P / r ->
  m%:R * r ^+ m.-1 * (4 * q * 1 * (2 * r)^-1) * - (P^-1) ^+ 2 * E +
    P^-1 * (- a / 4 * (1 * - (s^-1) ^+ 2) * E) =
  ((4 * s ^+ 2)^-1 * a - (2 * s)^-1 * m%:R) * (P^-1 * E).
Proof.
move=> hs hr hP hr2 hpow; rewrite hpow.
have e4 : 4 * q = r ^+ 2 / s by rewrite hr2; field.
by rewrite e4; field; rewrite hP hs hr.
Qed.

(** Source for [dgpr_power_pred]: m r^(m-1) = m r^m / r for r != 0;
    blueprint lem:kernel(3). *)
Lemma dgpr_power_pred (r : R) (m : nat) : r != 0 -> m%:R * r ^+ m.-1 = m%:R * r ^+ m / r.
Proof.
move=> hr; case: m => [|m]; first by rewrite !mul0r.
by rewrite exprS; field.
Qed.

(** Source for [dgpr_kernel_time_derivative]: DPGPR 2026, section 3;
    blueprint lem:kernel(3), proof: the derivative of [t |-> p_t(z)] at s is
    ((4s^2)^(-1) |z|^2 - n (2s)^(-1)) p_s(z), on the domain {t : 0 < t}. *)
Theorem dgpr_kernel_time_derivative (s : R) (z : X) : 0 < s ->
  has_norm_differential A1 A1 (fun t : R => 0 < t) (fun t : R^o => (p t z : R^o)) s
    (scalar_coefficient_linear_map
      (((4 * s ^+ 2)^-1 * N z ^+ 2 - (2 * s)^-1 * n%:R) * p s z : R^o)).
Proof.
move=> hs.
have hpi := @dgpr_pi_gt0 R.
have hT := dgpr_positive_interior hs.
have hid := @scalar_identity_coefficient_differential R (fun t => 0 < t) s hT.
have h1 := norm_differential_scale hA hA (4 * dgpr_pi R) hid.
rewrite dgpr_scm_scale in h1.
have h4ps : 0 < 4 * dgpr_pi R * s by rewrite mulr_gt0 // mulr_gt0.
have hsq : has_norm_differential A1 A1 (fun t : R => 0 < t) Num.sqrt
    ((4 * dgpr_pi R) *: (s : R^o))
    (@scalar_coefficient_linear_map R R^o ((2 * Num.sqrt (4 * dgpr_pi R * s))^-1)).
  exact: scalar_square_root_differential h4ps.
have hpos4 (x : R) : 0 < x -> 0 < (4 * dgpr_pi R) *: (x : R^o).
  by move=> hx; change (0 < 4 * dgpr_pi R * x); rewrite mulr_gt0 // mulr_gt0.
have hpowne (x : R) : 0 < x -> Num.sqrt ((4 * dgpr_pi R) *: (x : R^o)) ^+ n != 0.
  by move=> hx; rewrite expf_neq0 // gt_eqF // sqrtr_gt0 hpos4.
have hne (x : R) : 0 < x -> x != 0 by move=> hx; rewrite lt0r_neq0.
have h2 := norm_curve_chain_on_domain hA hpos4 h1 hsq.
have h3 := @norm_curve_power_differential R _ _ s _ n h2.
have hrne : Num.sqrt (4 * dgpr_pi R * s) ^+ n != 0.
  by rewrite expf_neq0 // gt_eqF // sqrtr_gt0.
have hr : has_norm_differential A1 A1 (fun t : R => t != 0) (fun t : R => t^-1)
    (Num.sqrt ((4 * dgpr_pi R) *: (s : R^o)) ^+ n)
    (@scalar_coefficient_linear_map R R^o (- ((Num.sqrt (4 * dgpr_pi R * s) ^+ n)^-1) ^+ 2)).
  exact: scalar_reciprocal_differential hrne.
have h4 := norm_curve_chain_on_domain hA hpowne h3 hr.
have hrs := @scalar_reciprocal_differential R s (lt0r_neq0 hs).
have h5 := norm_curve_chain_on_domain hA hne hid hrs.
have h6 := norm_differential_scale hA hA (- N z ^+ 2 / 4) h5.
rewrite dgpr_scm_scale in h6.
have hE := @real_exponential_differential R ((- N z ^+ 2 / 4) *: ((s : R^o)^-1)).
rewrite dgpr_exponential_term in hE.
have h7 := norm_curve_chain_on_domain hA (fun _ _ => Logic.I) h6 hE.
have h8 := norm_curve_scalar_product hA h4 h7.
have hr0 : Num.sqrt (4 * dgpr_pi R * s) != 0 by rewrite gt_eqF // sqrtr_gt0.
have hr2 : Num.sqrt (4 * dgpr_pi R * s) ^+ 2 = 4 * dgpr_pi R * s by rewrite sqr_sqrtr // ltW.
have ex (t : R) : - N z ^+ 2 / (4 * t) = - N z ^+ 2 / 4 * t^-1 by rewrite invfM mulrA.
move: h8.
match goal with |- has_norm_differential _ _ _ ?f _ (scalar_coefficient_linear_map ?V) -> _ =>
  (have ef : f = (fun t : R^o => (p t z : R^o)) by
    apply: funext => t; rewrite /dgpr_heat_kernel ex;
    change (Num.sqrt (4 * dgpr_pi R * t) ^- n * exp (- N z ^+ 2 / 4 * t^-1) =
      Num.sqrt (4 * dgpr_pi R * t) ^- n * exp (- N z ^+ 2 / 4 * t^-1)));
  (have eV : V = ((4 * s ^+ 2)^-1 * N z ^+ 2 - (2 * s)^-1 * n%:R) * p s z by
    change (n%:R * Num.sqrt (4 * dgpr_pi R * s) ^+ n.-1 *
      (4 * dgpr_pi R * 1 * (2 * Num.sqrt (4 * dgpr_pi R * s))^-1) *
      - (Num.sqrt (4 * dgpr_pi R * s) ^- n) ^+ 2 * exp (- N z ^+ 2 / 4 * s^-1) +
      Num.sqrt (4 * dgpr_pi R * s) ^- n *
      (- N z ^+ 2 / 4 * (1 * - (s^-1) ^+ 2) * exp (- N z ^+ 2 / 4 * s^-1)) =
      ((4 * s ^+ 2)^-1 * N z ^+ 2 - (2 * s)^-1 * n%:R) * p s z);
    rewrite /dgpr_heat_kernel ex;
    exact: (@dgpr_time_algebra s (dgpr_pi R) (N z ^+ 2) (exp (- N z ^+ 2 / 4 * s^-1)) _ _ n
      (lt0r_neq0 hs) hr0 hrne hr2 (dgpr_power_pred _ hr0)))
end.
by rewrite ef eV.
Qed.

(** Source for [dgpr_kernel_heat]: DPGPR 2026, section 3; blueprint
    lem:kernel(3), the heat equation partial_s p_s(z) = Delta p_s(z), where
    Delta p_s(z) is the sum over the standard basis e_1, ..., e_n of
    D^2 p_s(z)(e_i, e_i). *)
Theorem dgpr_kernel_heat (s : R) (z : X) : 0 < s ->
  has_normed_curve_derivative A1 (fun t : R => (p t z : R^o)) s
    (\sum_(i < n) dgpr_kernel_second s z (@coordinate_basis R n i) (@coordinate_basis R n i)).
Proof.
move=> hs; have h := dgpr_kernel_time_derivative z hs.
have [_ hc] := (norm_differential_real_source hA _ _ _ _).1 h.
have e1 : @scalar_coefficient_linear_map R R^o
    (((4 * s ^+ 2)^-1 * N z ^+ 2 - (2 * s)^-1 * n%:R) * p s z) 1 =
    \sum_(i < n) dgpr_kernel_second s z (@coordinate_basis R n i) (@coordinate_basis R n i).
  change (1 * (((4 * s ^+ 2)^-1 * N z ^+ 2 - (2 * s)^-1 * n%:R) * p s z) =
    \sum_(i < n) dgpr_kernel_second s z (@coordinate_basis R n i) (@coordinate_basis R n i)).
  rewrite mul1r (eq_bigr (fun i => ((4 * s ^+ 2)^-1 * (z i * z i) - (2 * s)^-1) * p s z)).
    rewrite -big_distrl /= sumrB -mulr_sumr sumr_const card_ord -[(2 * s)^-1 *+ n]mulr_natr.
    by rewrite inner_norm_sqr /euclidean_inner_product.
  move=> i _; rewrite dgpr_kernel_secondE !(euclidean_inner_basis z).
  by rewrite -(inner_norm_sqr (@euclidean_inner_productP R n)) euclidean_coordinate_unit_norm
    expr1n mulr1 (mulrA ((4 * s ^+ 2)^-1)).
by rewrite -e1.
Qed.

(** Source for [dgpr_kernel_formulas]: DPGPR 2026, section 3; blueprint
    lem:kernel(5), both formulas together. *)
Theorem dgpr_kernel_formulas (s : R) (z v : X) : 0 < s ->
  has_norm_differential N A1 setT (p s) z (dgpr_kernel_differential s z) /\
  (forall w, dgpr_kernel_differential s z w = - (2 * s)^-1 * B z w * p s z) /\
  has_norm_differential N A1 setT (fun x : X => dgpr_kernel_differential s x v) z
    (dgpr_kernel_second s z v) /\
  (forall w, dgpr_kernel_second s z v w =
    ((4 * s ^+ 2)^-1 * B z v * B z w - (2 * s)^-1 * B v w) * p s z).
Proof.
move=> hs; split; first exact: dgpr_kernel_differential_formula.
split; first by move=> w; exact: dgpr_kernel_differentialE.
split; first exact: dgpr_kernel_second_formula.
by move=> w; exact: dgpr_kernel_secondE.
Qed.

End HeatKernelDifferential.
