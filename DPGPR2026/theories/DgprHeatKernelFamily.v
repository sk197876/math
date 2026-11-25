(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3; blueprint
    dgpr_blueprint.tex, proofs of lem:kernel(4) and lem:heat_extension(1).
    The kernel family is the smallest family of functions q(s,z) of a time
    s and a point z of R^n which contains p_s(z) and is closed under
    addition, multiplication by constants, multiplication by a coordinate
    z_i and multiplication by s^(-1). Its members are the products of p_s(z)
    with polynomials in s^(-1) and z. The family contains the partial
    derivatives of its members in s and in the coordinates of z, and on
    every strip a <= s <= b with 0 < a each member decays faster than every
    power of (1 + |z|^2)^(-1), uniformly in s. These are the facts used for
    differentiation under the integral sign in the heat extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerNormInequalities RealExponentialUP RealExponentialSealed RealExponentialDifferential
  NormDifferentialUP NormDifferentialLocal NormClassOneUP NormClassOneLaws NormClassZeroArithmetic
  NormClassZeroScalarProduct NormClassZeroComposition NormClassHigherRestriction NormOpenDomainLaws
  NormClassHigherDerivative NormPartialDerivative NormedCurveDerivativeUP RealCurveDerivativeUP RealCurveDerivativeLaws ScalarReciprocalDifferential NormHigherCurveDerivativeUP
  PuncturedRealLinearLimits RealCurveDerivativeAlgebra RealCurvePolynomialDerivatives ScalarAbsoluteValueCurve
  ScalarCoefficientLinearAlgebra FiniteCoordinates CoordinateProjection EuclideanCoordinateMetric
  CircularTrigonometrySealed.
From DPGPR Require Import DgprHeatKernel DgprHeatKernelDifferential DgprHeatExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section RealCurves.
Variable R : realType.

(** Source for [dgpr_real_curve_add]: the derivative of a sum, Federer
    2.9.19, p. 163; blueprint lem:heat_extension(1). *)
Lemma dgpr_real_curve_add (f g : R -> R) (a v w : R) :
  has_real_curve_derivative f a v -> has_real_curve_derivative g a w ->
  has_real_curve_derivative (fun t => f t + g t) a (v + w).
Proof.
move=> hf hg; apply: (@punctured_real_limit_congr R
  (fun h => (f (a + h) - f a) / h + (g (a + h) - g a) / h)).
  by move=> h _; rewrite -mulrDl opprD addrACA.
exact: punctured_real_limit_add hf hg.
Qed.

(** Source for [dgpr_real_curve_affine]: the derivative of
    [t |-> c + t d] is d, Federer 2.9.19, p. 163; blueprint
    lem:heat_extension(1). *)
Lemma dgpr_real_curve_affine (c d a : R) :
  has_real_curve_derivative (fun t => c + t * d) a d.
Proof.
apply: (@punctured_real_limit_congr R (fun _ => d)).
  by move=> h hh; rewrite /= opprD addrACA subrr add0r -mulrBl addrAC subrr add0r mulrAC mulfV // mul1r.
exact: punctured_real_constant_limit.
Qed.

(** Source for [dgpr_real_curve_shift]: translation of the parameter of
    a real curve, Federer 2.9.19, p. 163; blueprint lem:heat_extension(1). *)
Lemma dgpr_real_curve_shift (f : R -> R) (a v : R) :
  has_real_curve_derivative f a v <-> has_real_curve_derivative (fun t => f (a + t)) 0 v.
Proof.
rewrite /has_real_curve_derivative.
have -> : (fun h => (f (a + (0 + h)) - f (a + 0)) / h) = (fun h => (f (a + h) - f a) / h).
  by apply: funext => h; rewrite add0r addr0.
by [].
Qed.
End RealCurves.

Section KernelFamily.
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
Local Notation e := (@coordinate_basis R n).

(** Source for [dgpr_kernel_family]: the functions [(s,z) |-> P(s^(-1),z)
    p_s(z)] with a polynomial P, which carry the derivatives of p_s in the
    proof of lem:kernel(4), blueprint section 3 (there D^j p_1 = P_j p_1);
    they are generated from p by sums, constant multiples, multiplication
    by a coordinate z_i and multiplication by s^(-1). *)
Inductive dgpr_kernel_family : (R -> X -> R) -> Prop :=
| dgpr_kernel_family_base : dgpr_kernel_family p
| dgpr_kernel_family_coordinate (i : 'I_n) (q : R -> X -> R) :
    dgpr_kernel_family q -> dgpr_kernel_family (fun s z => z i * q s z)
| dgpr_kernel_family_reciprocal (q : R -> X -> R) :
    dgpr_kernel_family q -> dgpr_kernel_family (fun s z => s^-1 * q s z)
| dgpr_kernel_family_add (q1 q2 : R -> X -> R) :
    dgpr_kernel_family q1 -> dgpr_kernel_family q2 ->
    dgpr_kernel_family (fun s z => q1 s z + q2 s z)
| dgpr_kernel_family_scale (c : R) (q : R -> X -> R) :
    dgpr_kernel_family q -> dgpr_kernel_family (fun s z => c * q s z).

(** Source for [dgpr_kernel_family_zero]: the zero function belongs to
    the kernel family; supporting lem:kernel(4). *)
Lemma dgpr_kernel_family_zero : dgpr_kernel_family (fun (_ : R) (_ : X) => 0).
Proof.
have -> : (fun (_ : R) (_ : X) => 0 : R) = (fun s z => 0 * p s z).
  by apply: funext => s; apply: funext => z; rewrite mul0r.
exact (dgpr_kernel_family_scale 0 dgpr_kernel_family_base).
Qed.

(** Source for [dgpr_kernel_family_big]: finite sums of members belong to
    the kernel family; supporting lem:kernel(4). *)
Lemma dgpr_kernel_family_big (I : Type) (r : seq I) (F : I -> R -> X -> R) :
  (forall i, dgpr_kernel_family (F i)) ->
  dgpr_kernel_family (fun s z => \sum_(i <- r) F i s z).
Proof.
move=> hF; elim: r => [|i r IH].
  have -> : (fun s z => \sum_(i <- [::]) F i s z) = (fun (_ : R) (_ : X) => 0 : R).
    by apply: funext => s; apply: funext => z; rewrite big_nil.
  exact: dgpr_kernel_family_zero.
have -> : (fun s z => \sum_(j <- i :: r) F j s z) = (fun s z => F i s z + \sum_(j <- r) F j s z).
  by apply: funext => s; apply: funext => z; rewrite big_cons.
exact (dgpr_kernel_family_add (hF i) IH).
Qed.

(** Source for [dgpr_exponential_nat_scale]: exp(k x) = exp(x)^k, from
    the addition law of the exponential; supporting lem:kernel(4). *)
Lemma dgpr_exponential_nat_scale (x : R) (k : nat) : exp (k%:R * x) = exp x ^+ k.
Proof.
elim: k => [|k IH]; first by rewrite mul0r expr0 (real_exponential_zero (@RealExponential.laws R)).
by rewrite exprSr -IH -(real_exponential_add (@RealExponential.laws R)) -addn1 natrD mulrDl mul1r.
Qed.

(** Source for [dgpr_polynomial_exponential_weight]: (1 + q)^k exp(-q) <=
    (k+1)^k for 0 <= q, since exp(q) >= (1 + q/(k+1))^(k+1); supporting
    lem:kernel(4). *)
Lemma dgpr_polynomial_exponential_weight (q : R) (k : nat) : 0 <= q ->
  (1 + q) ^+ k * exp (- q) <= (k.+1)%:R ^+ k.
Proof.
move=> hq; set m := (k.+1)%:R.
have hm : 0 < m by rewrite /m ltr0n.
have hm1 : 1 <= m by rewrite /m ler1n.
have hP := real_exponential_positive (@RealExponential.laws R).
have hqm : 0 <= q / m by rewrite divr_ge0 // ltW.
have h1 : 1 + q <= m * (1 + q / m) by rewrite mulrDr mulr1 mulrC divfK ?lt0r_neq0 // lerD2r.
have h1q : 0 <= 1 + q by rewrite addr_ge0.
have hmq : 0 <= m * (1 + q / m) by rewrite mulr_ge0 ?addr_ge0 // ltW.
have h2 : (1 + q) ^+ k <= (m * (1 + q / m)) ^+ k.
  by apply: lerXn2r; rewrite ?nnegrE.
have h3 : (1 + q / m) ^+ k <= exp q.
  have hb : 1 <= 1 + q / m by rewrite lerDl.
  have h4 : (1 + q / m) ^+ k <= (1 + q / m) ^+ k.+1.
    rewrite exprSr -[X in X <= _]mulr1 ler_wpM2l //.
    by rewrite exprn_ge0 // addr_ge0.
  apply: le_trans h4 _.
  have h5 : (1 + q / m) ^+ k.+1 <= exp (q / m) ^+ k.+1.
    have hq1 : 0 <= 1 + q / m by rewrite addr_ge0.
    have he1 : 0 <= exp (q / m) := ltW (hP _).
    have ht := real_exponential_tangent (@RealExponential.laws R) (q / m).
    by apply: lerXn2r; rewrite ?nnegrE.
  apply: le_trans h5 _.
  by rewrite -dgpr_exponential_nat_scale -/m mulrC divfK ?lt0r_neq0.
have hE : exp q * exp (- q) = 1.
  by rewrite -(real_exponential_add (@RealExponential.laws R)) subrr
    (real_exponential_zero (@RealExponential.laws R)).
have hpos : 0 <= exp (- q) := ltW (hP _).
have h6 : (1 + q / m) ^+ k * exp (- q) <= 1.
  rewrite -[X in _ <= X]hE; exact: (@ler_wpM2r _ (exp (- q)) hpos _ _ h3).
apply: le_trans (ler_wpM2r hpos h2) _.
rewrite exprMn -mulrA.
have hmk : 0 <= m ^+ k by rewrite exprn_ge0 // ltW.
by have := ler_wpM2l hmk h6; rewrite mulr1.
Qed.

(** Source for [dgpr_kernel_constant_antitone]: (4 pi s)^(-n/2) <=
    (4 pi a)^(-n/2) for 0 < a <= s; supporting lem:kernel(4). *)
Lemma dgpr_kernel_constant_antitone (a s : R) : 0 < a -> a <= s ->
  dgpr_kernel_constant n s <= dgpr_kernel_constant n a.
Proof.
move=> ha has; have hs : 0 < s := lt_le_trans ha has.
have hpi := @dgpr_pi_gt0 R.
have hpa : 0 < Num.sqrt (4 * dgpr_pi R * a) by rewrite sqrtr_gt0 !mulr_gt0.
have hps : 0 < Num.sqrt (4 * dgpr_pi R * s) by rewrite sqrtr_gt0 !mulr_gt0.
rewrite /dgpr_kernel_constant lef_pV2 ?posrE ?exprn_gt0 //.
have hle : Num.sqrt (4 * dgpr_pi R * a) <= Num.sqrt (4 * dgpr_pi R * s).
  have h4p : 0 < 4 * dgpr_pi R by rewrite mulr_gt0.
  have hs0 : 0 <= 4 * dgpr_pi R * s by rewrite mulr_ge0 // ltW.
  by rewrite ler_sqrt // ler_pM2l.
have hpa0 := ltW hpa; have hps0 := ltW hps.
by apply: lerXn2r; rewrite ?nnegrE.
Qed.

(** Source for [dgpr_coordinate_abs_le]: |z_i| <= |z|, by the
    Cauchy-Schwarz inequality, Federer 1.7.1; supporting lem:kernel(4). *)
Lemma dgpr_coordinate_abs_le (z : X) (i : 'I_n) : `|z i| <= N z.
Proof.
rewrite -(euclidean_inner_basis z i).
have h := inner_cauchy (@euclidean_inner_productP R n) z (e i).
by rewrite (euclidean_coordinate_unit_norm R i) mulr1 in h.
Qed.

(** Source for [dgpr_norm_le_weight]: |z| <= 1 + |z|^2; supporting
    lem:kernel(4). *)
Lemma dgpr_norm_le_weight (z : X) : N z <= 1 + N z ^+ 2.
Proof. have := sqr_ge0 (N z - 1 / 2); rewrite sqrrB expr2 => h; nra. Qed.

(** Source for [dgpr_kernel_family_bound]: every member q of the kernel
    family satisfies (1 + |z|^2)^k |q(s,z)| <= C for a <= s <= b, with C
    depending on q, a, b and k; this is the uniform decay behind
    lem:kernel(4) and the domination in the proof of
    lem:heat_extension(1). *)
Lemma dgpr_kernel_family_bound (q : R -> X -> R) : dgpr_kernel_family q ->
  forall a b : R, 0 < a -> forall k : nat, exists C : R, forall s z, a <= s -> s <= b ->
    (1 + N z ^+ 2) ^+ k * `|q s z| <= C.
Proof.
elim => [|i q' hq IH|q' hq IH|q1 q2 h1 IH1 h2 IH2|c q' hq IH] a b ha k.
- exists ((1 + 4 * b) ^+ k * dgpr_kernel_constant n a * (k.+1)%:R ^+ k) => s z has hsb.
  have hs : 0 < s := lt_le_trans ha has.
  have hb : 0 < b := lt_le_trans hs hsb.
  rewrite (gtr0_norm (dgpr_kernel_gt0 z hs)).
  have h4 : 0 < 4 * s by rewrite mulr_gt0.
  set u := N z ^+ 2 / (4 * s).
  have hu : 0 <= u by rewrite divr_ge0 ?sqr_ge0 // ltW.
  have e1 : N z ^+ 2 = 4 * s * u by rewrite /u mulrC divfK // lt0r_neq0.
  rewrite /dgpr_heat_kernel (mulNr (N z ^+ 2)) -/u -/(dgpr_kernel_constant n s).
  have hw : 1 + N z ^+ 2 <= (1 + 4 * b) * (1 + u).
    have hbs : 0 <= b - s by rewrite subr_ge0.
    rewrite e1; have := mulr_ge0 hu hbs; nra.
  have hb4 : 0 <= 1 + 4 * b by rewrite addr_ge0 // mulr_ge0 // ltW.
  have hw0 : 0 <= 1 + N z ^+ 2 by rewrite addr_ge0 ?sqr_ge0.
  have hu1 : 0 <= 1 + u by rewrite addr_ge0.
  have hw1 := mulr_ge0 hb4 hu1.
  have hw2 : (1 + N z ^+ 2) ^+ k <= ((1 + 4 * b) * (1 + u)) ^+ k.
    by apply: lerXn2r; rewrite ?nnegrE.
  have hc := dgpr_kernel_constant_antitone ha has.
  have hc0 := dgpr_kernel_constant_ge0 n s.
  have hE : 0 <= exp (- u) := ltW (real_exponential_positive (@RealExponential.laws R) _).
  have hW := dgpr_polynomial_exponential_weight k hu.
  apply: le_trans (ler_wpM2r (mulr_ge0 hc0 hE) hw2) _.
  rewrite exprMn.
  have -> : (1 + 4 * b) ^+ k * (1 + u) ^+ k * (dgpr_kernel_constant n s * exp (- u)) =
    (1 + 4 * b) ^+ k * dgpr_kernel_constant n s * ((1 + u) ^+ k * exp (- u)) by ring.
  apply: ler_pM => //.
  + by rewrite mulr_ge0 ?exprn_ge0.
  + by rewrite mulr_ge0 ?exprn_ge0 // addr_ge0.
  + by rewrite ler_wpM2l ?exprn_ge0.
- have [C hC] := IH a b ha k.+1.
  exists C => s z has hsb.
  apply: le_trans (hC s z has hsb).
  rewrite normrM (exprSr (1 + N z ^+ 2)) -mulrA ler_wpM2l ?exprn_ge0 ?addr_ge0 ?sqr_ge0 //.
  apply: ler_wpM2r; first exact: normr_ge0.
  exact: le_trans (dgpr_coordinate_abs_le z i) (dgpr_norm_le_weight z).
- have [C hC] := IH a b ha k.
  exists (a^-1 * C) => s z has hsb.
  have hs : 0 < s := lt_le_trans ha has.
  have hsi : 0 < s^-1 by rewrite invr_gt0.
  have hai : 0 <= a^-1 by rewrite invr_ge0 ltW.
  have hw0 : 0 <= (1 + N z ^+ 2) ^+ k * `|q' s z| by rewrite mulr_ge0 ?exprn_ge0 ?addr_ge0 ?sqr_ge0.
  have hle : s^-1 <= a^-1 by rewrite lef_pV2 ?posrE.
  rewrite normrM mulrCA (gtr0_norm hsi).
  exact: ler_pM (ltW hsi) hw0 hle (hC s z has hsb).
- have [C1 hC1] := IH1 a b ha k; have [C2 hC2] := IH2 a b ha k.
  exists (C1 + C2) => s z has hsb.
  apply: le_trans (lerD (hC1 s z has hsb) (hC2 s z has hsb)).
  rewrite -mulrDr ler_wpM2l ?exprn_ge0 ?addr_ge0 ?sqr_ge0 //.
  exact: ler_normD.
- have [C hC] := IH a b ha k.
  exists (`|c| * C) => s z has hsb.
  rewrite normrM mulrCA ler_wpM2l //; exact: hC.
Qed.

(** Source for [dgpr_coordinate_class_zero]: continuity of the coordinate
    [z |-> z_i]; supporting lem:heat_extension(1). *)
Lemma dgpr_coordinate_class_zero (i : 'I_n) : norm_class_zero N A1 setT (fun z : X => z i).
Proof.
have -> : (fun z : X => z i) = (fun z : X => B z (e i)).
  by apply: funext => z; rewrite euclidean_inner_basis.
exact: dgpr_inner_class_zero.
Qed.

(** Source for [dgpr_kernel_family_class_zero]: for 0 < s every member of
    the kernel family is continuous in z; supporting
    lem:heat_extension(1). *)
Lemma dgpr_kernel_family_class_zero (q : R -> X -> R) : dgpr_kernel_family q ->
  forall s, 0 < s -> norm_class_zero N A1 setT (q s).
Proof.
elim => [|i q' hq IH|q' hq IH|q1 q2 h1 IH1 h2 IH2|c q' hq IH] s hs.
- exact: dgpr_kernel_class_zero.
- exact: (norm_class_zero_scalar_product hA (dgpr_coordinate_class_zero i) (IH s hs)).
- exact: (norm_class_zero_scale hA s^-1 (IH s hs)).
- exact: (norm_class_zero_add hA (IH1 s hs) (IH2 s hs)).
- exact: (norm_class_zero_scale hA c (IH s hs)).
Qed.

(** Source for [dgpr_kernel_space_partial]: the partial derivative of p_s
    in the direction e_i is -(2s)^(-1) z_i p_s(z), lem:kernel(5);
    supporting lem:heat_extension(1). *)
Lemma dgpr_kernel_space_partial (s : R) (z : X) (i : 'I_n) : 0 < s ->
  has_real_curve_derivative (fun t => p s (z + t *: e i)) 0
    ((- 2^-1) * (s^-1 * (z i * p s z))).
Proof.
move=> hs; have hd := norm_differential_partial hN hA (dgpr_kernel_differential_formula z hs) i.
move: hd; rewrite /has_norm_partial_derivative /has_real_curve_derivative dgpr_kernel_differentialE
  euclidean_inner_basis.
have -> : - (2 * s)^-1 * z i * p s z = (- 2^-1) * (s^-1 * (z i * p s z)).
  by rewrite invfM; ring.
move=> h e0 he0; have [d [hd hd']] := h e0 he0.
exists d; split => // t ht; have := hd' t ht.
rewrite /= !add0r scale0r addr0 [_ / t]mulrC => hlt; exact: hlt.
Qed.

(** Source for [dgpr_kernel_time_member]: the function
    ((4s^2)^(-1)|z|^2 - n (2s)^(-1)) p_s(z) of lem:kernel(3), written as
    a combination of generators of the kernel family. *)
Definition dgpr_kernel_time_member (s : R) (z : X) : R :=
  4^-1 * (s^-1 * (s^-1 * \sum_(i < n) z i * (z i * p s z))) + (- (n%:R / 2)) * (s^-1 * p s z).

(** Source for [dgpr_kernel_time_member_family]: the time derivative of
    p_s belongs to the kernel family; lem:kernel(3). *)
Lemma dgpr_kernel_time_member_family : dgpr_kernel_family dgpr_kernel_time_member.
Proof.
have h1 : dgpr_kernel_family (fun s z => \sum_(i < n) z i * (z i * p s z)) :=
  dgpr_kernel_family_big (index_enum 'I_n)
    (fun i => dgpr_kernel_family_coordinate i (dgpr_kernel_family_coordinate i dgpr_kernel_family_base)).
exact: (dgpr_kernel_family_add
  (dgpr_kernel_family_scale 4^-1 (dgpr_kernel_family_reciprocal (dgpr_kernel_family_reciprocal h1)))
  (dgpr_kernel_family_scale (- (n%:R / 2)) (dgpr_kernel_family_reciprocal dgpr_kernel_family_base))).
Qed.

(** Source for [dgpr_kernel_time_memberE]: the member equals
    ((4s^2)^(-1)|z|^2 - n (2s)^(-1)) p_s(z); lem:kernel(3). *)
Lemma dgpr_kernel_time_memberE (s : R) (z : X) : 0 < s ->
  dgpr_kernel_time_member s z = ((4 * s ^+ 2)^-1 * N z ^+ 2 - (2 * s)^-1 * n%:R) * p s z.
Proof.
move=> hs; have hs0 : s != 0 := lt0r_neq0 hs.
have hsum : \sum_(i < n) z i * (z i * p s z) = N z ^+ 2 * p s z.
  rewrite (inner_norm_sqr (@euclidean_inner_productP R n) z) /euclidean_inner_product big_distrl /=.
  by apply: eq_bigr => i _; rewrite mulrA.
rewrite /dgpr_kernel_time_member hsum.
move: (N z ^+ 2) (p s z) => a P.
by field.
Qed.

(** Source for [dgpr_kernel_time_curve]: the derivative of [t |-> p_t(z)]
    at 0 < s; lem:kernel(3). *)
Lemma dgpr_kernel_time_curve (s : R) (z : X) : 0 < s ->
  has_real_curve_derivative (fun t => p t z) s (dgpr_kernel_time_member s z).
Proof.
move=> hs; rewrite dgpr_kernel_time_memberE //.
exact: (real_curve_derivative_from_differential (dgpr_kernel_time_derivative z hs)).
Qed.

(** Source for [dgpr_kernel_family_space_derivative]: the partial
    derivatives in z of a member of the kernel family are members of the
    kernel family; supporting lem:kernel(4) and lem:heat_extension(1). *)
Lemma dgpr_kernel_family_space_derivative (q : R -> X -> R) : dgpr_kernel_family q ->
  forall i : 'I_n, exists q', dgpr_kernel_family q' /\
    forall s z, 0 < s -> has_real_curve_derivative (fun t => q s (z + t *: e i)) 0 (q' s z).
Proof.
elim => [|j q' hq IH|q' hq IH|q1 q2 h1 IH1 h2 IH2|c q' hq IH] i.
- exists (fun (s : R) (z : X) => (- 2^-1) * (s^-1 * (z i * p s z))); split.
    exact: (dgpr_kernel_family_scale _ (dgpr_kernel_family_reciprocal
      (dgpr_kernel_family_coordinate i dgpr_kernel_family_base))).
  by move=> s z hs; exact: dgpr_kernel_space_partial.
- have [qi [hqi hqi']] := IH i.
  exists (fun (s : R) (z : X) => e i j * q' s z + z j * qi s z); split.
    exact: (dgpr_kernel_family_add (dgpr_kernel_family_scale (e i j) hq) (dgpr_kernel_family_coordinate j hqi)).
  move=> s z hs.
  have hc : has_real_curve_derivative (fun t => (z + t *: e i) j) 0 (e i j).
    have -> : (fun t => (z + t *: e i) j) = (fun t => z j + t * e i j).
      by apply: funext => t; rewrite !ffunE.
    exact: dgpr_real_curve_affine.
  have hp := real_curve_derivative_product hc (hqi' s z hs).
  move: hp; rewrite /= scale0r addr0 => hp; exact: hp.
- have [qi [hqi hqi']] := IH i.
  exists (fun (s : R) (z : X) => s^-1 * qi s z); split; first exact (dgpr_kernel_family_reciprocal hqi).
  move=> s z hs; exact: (@real_curve_derivative_scale R _ _ _ s^-1 (hqi' s z hs)).
- have [r1 [hr1 hr1']] := IH1 i; have [r2 [hr2 hr2']] := IH2 i.
  exists (fun (s : R) (z : X) => r1 s z + r2 s z); split; first exact (dgpr_kernel_family_add hr1 hr2).
  move=> s z hs; exact: dgpr_real_curve_add (hr1' s z hs) (hr2' s z hs).
- have [qi [hqi hqi']] := IH i.
  exists (fun (s : R) (z : X) => c * qi s z); split; first exact (dgpr_kernel_family_scale c hqi).
  move=> s z hs; exact: (@real_curve_derivative_scale R _ _ _ c (hqi' s z hs)).
Qed.

(** Source for [dgpr_kernel_family_time_derivative]: the partial
    derivative in s of a member of the kernel family is a member of the
    kernel family; supporting lem:kernel(3) and lem:heat_extension(1). *)
Lemma dgpr_kernel_family_time_derivative (q : R -> X -> R) : dgpr_kernel_family q ->
  exists q', dgpr_kernel_family q' /\
    forall s z, 0 < s -> has_real_curve_derivative (fun t => q t z) s (q' s z).
Proof.
elim => [|j q' hq IH|q' hq IH|q1 q2 h1 IH1 h2 IH2|c q' hq IH].
- exists dgpr_kernel_time_member; split; first exact: dgpr_kernel_time_member_family.
  exact: dgpr_kernel_time_curve.
- have [r [hr hr']] := IH.
  exists (fun (s : R) (z : X) => z j * r s z); split; first exact (dgpr_kernel_family_coordinate j hr).
  move=> s z hs; exact: (@real_curve_derivative_scale R _ _ _ (z j) (hr' s z hs)).
- have [r [hr hr']] := IH.
  exists (fun (s : R) (z : X) => (-1) * (s^-1 * (s^-1 * q' s z)) + s^-1 * r s z); split.
    exact: (dgpr_kernel_family_add (dgpr_kernel_family_scale (-1)
      (dgpr_kernel_family_reciprocal (dgpr_kernel_family_reciprocal hq))) (dgpr_kernel_family_reciprocal hr)).
  move=> s z hs /=.
  have hi := real_curve_reciprocal_actual_derivative (lt0r_neq0 hs).
  have hp := real_curve_derivative_product hi (hr' s z hs).
  have -> : (-1) * (s^-1 * (s^-1 * q' s z)) + s^-1 * r s z =
    - ((s^-1) ^+ 2) * q' s z + s^-1 * r s z by rewrite expr2; ring.
  exact: hp.
- have [r1 [hr1 hr1']] := IH1; have [r2 [hr2 hr2']] := IH2.
  exists (fun (s : R) (z : X) => r1 s z + r2 s z); split; first exact (dgpr_kernel_family_add hr1 hr2).
  move=> s z hs; exact: dgpr_real_curve_add (hr1' s z hs) (hr2' s z hs).
- have [r [hr hr']] := IH.
  exists (fun (s : R) (z : X) => c * r s z); split; first exact (dgpr_kernel_family_scale c hr).
  move=> s z hs; exact: (@real_curve_derivative_scale R _ _ _ c (hr' s z hs)).
Qed.
End KernelFamily.

Arguments dgpr_kernel_family_bound [R n q] _ a b _ k.

Section JointContinuity.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation W := (R_n R n.+1).
Local Notation NW := (inner_norm (@euclidean_inner_productP R n.+1)).
Local Notation hNW := (inner_norm_real_norm (@euclidean_inner_productP R n.+1)).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation exp := (@RealExponential.exponential R).
Local Notation p := (@dgpr_heat_kernel R n).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).

(** Source for [dgpr_space_part]: the point x of R^n of a point (s,x) of
    R x R^n = R^(n+1), whose coordinate 0 is the time s; blueprint
    def:heat, where u is a map of (0,infinity) x R^n. *)
Definition dgpr_space_part (w : W) : X := [ffun i => w (lift ord0 i)].

(** Source for [dgpr_positive_time]: the half space (0,infinity) x R^n of
    R^(n+1), the domain of the heat extension in def:heat. *)
Definition dgpr_positive_time : set W := [set w | 0 < w ord0].

(** Source for [dgpr_positive_time_interior]: the half space is open;
    supporting lem:heat_extension(1). *)
Lemma dgpr_positive_time_interior (w : W) :
  dgpr_positive_time w -> norm_domain_interior NW dgpr_positive_time w.
Proof.
move=> hw; exists (w ord0); split => // h hh.
have hc := @dgpr_coordinate_abs_le R n.+1 h ord0.
have hn := ler_norm (- h ord0); rewrite normrN in hn.
rewrite /dgpr_positive_time /= ffunE.
move: hw; rewrite /dgpr_positive_time /= => hw; lra.
Qed.

(** Source for [dgpr_class_zero_ext]: continuity is a property of the
    values on the domain; supporting lem:heat_extension(1). *)
Lemma dgpr_class_zero_ext (f g : W -> R^o) : (forall w, f w = g w) ->
  norm_class_zero NW A1 dgpr_positive_time f -> norm_class_zero NW A1 dgpr_positive_time g.
Proof. by move=> e; apply: norm_class_zero_domain_agreement => w _; exact: e. Qed.

(** Source for [dgpr_half_coordinate_class_zero]: the coordinates of
    R^(n+1) are continuous on the half space; supporting
    lem:heat_extension(1). *)
Lemma dgpr_half_coordinate_class_zero (j : 'I_n.+1) :
  norm_class_zero NW A1 dgpr_positive_time (fun w : W => w j).
Proof.
apply: (@norm_class_zero_open_restriction R W R^o NW A1 setT dgpr_positive_time) => //.
  exact: dgpr_positive_time_interior.
exact: (@dgpr_coordinate_class_zero R n.+1 j).
Qed.

(** Source for [dgpr_half_constant_class_zero]: constants are continuous
    on the half space; supporting lem:heat_extension(1). *)
Lemma dgpr_half_constant_class_zero (c : R) :
  norm_class_zero NW A1 dgpr_positive_time (fun _ : W => (c : R^o)).
Proof. exact: (norm_class_zero_constant hA c dgpr_positive_time_interior). Qed.

(** Source for [dgpr_time_compose_class_zero]: if phi is continuous on
    (0,infinity), then [(s,x) |-> phi(s)] is continuous on the half space
    (Federer 3.1.1); supporting lem:heat_extension(1). *)
Lemma dgpr_time_compose_class_zero (phi : R -> R) :
  norm_class_zero A1 A1 (fun t : R => 0 < t) phi ->
  norm_class_zero NW A1 dgpr_positive_time (fun w : W => (phi (w ord0) : R^o)).
Proof.
move=> hphi.
have h := norm_class_zero_composition (dgpr_half_coordinate_class_zero ord0) hphi.
apply: (norm_class_zero_open_restriction (A := fun w => dgpr_positive_time w /\ 0 < w ord0)) h.
  by move=> w hw; split.
exact: dgpr_positive_time_interior.
Qed.

(** Source for [dgpr_whole_compose_class_zero]: if psi is continuous on
    R and g is continuous on the half space, so is psi o g (Federer 3.1.1);
    supporting lem:heat_extension(1). *)
Lemma dgpr_whole_compose_class_zero (psi : R -> R) (g : W -> R) :
  norm_class_zero A1 A1 (fun _ : R => True) psi ->
  norm_class_zero NW A1 dgpr_positive_time (fun w => (g w : R^o)) ->
  norm_class_zero NW A1 dgpr_positive_time (fun w : W => (psi (g w) : R^o)).
Proof.
move=> hpsi hg.
have h := norm_class_zero_composition hg hpsi.
apply: (norm_class_zero_open_restriction (A := fun w => dgpr_positive_time w /\ True)) h.
  by move=> w hw; split.
exact: dgpr_positive_time_interior.
Qed.

(** Source for [dgpr_reciprocal_class_zero]: [t |-> t^(-1)] is continuous
    on (0,infinity), by its differential (Federer 3.1.1); supporting
    lem:heat_extension(1). *)
Lemma dgpr_reciprocal_class_zero :
  norm_class_zero A1 A1 (fun t : R => 0 < t) (fun t : R => (t^-1 : R^o)).
Proof.
apply: (@norm_everywhere_differentiable_class_zero R R^o R^o A1 A1 hA _ _
  (fun a => @scalar_coefficient_linear_map R R^o (- ((a^-1) ^+ 2)))) => a ha.
apply: (norm_differential_restrict (A := fun t : R^o => t != 0)).
- by move=> t ht; exact: lt0r_neq0.
- exact: dgpr_positive_interior.
exact: (scalar_reciprocal_differential (lt0r_neq0 ha)).
Qed.

(** Source for [dgpr_exponential_class_zero]: the exponential is
    continuous, by its differential (Federer 3.1.1); supporting
    lem:heat_extension(1). *)
Lemma dgpr_exponential_class_zero :
  norm_class_zero A1 A1 (fun _ : R => True) (fun t : R => (exp t : R^o)).
Proof.
apply: (@norm_everywhere_differentiable_class_zero R R^o R^o A1 A1 hA _ _
  (fun a => real_exponential_linear_term a)) => a _.
exact: real_exponential_differential.
Qed.

(** Source for [dgpr_kernel_origin_class_zero]: [t |-> p_t(0)] =
    [t |-> (4 pi t)^(-n/2)] is continuous on (0,infinity), by
    lem:kernel(3); supporting lem:heat_extension(1). *)
Lemma dgpr_kernel_origin_class_zero :
  norm_class_zero A1 A1 (fun t : R => 0 < t) (fun t : R => (p t 0 : R^o)).
Proof.
apply: (@norm_everywhere_differentiable_class_zero R R^o R^o A1 A1 hA _ _
  (fun a => scalar_coefficient_linear_map
    (((4 * a ^+ 2)^-1 * N 0 ^+ 2 - (2 * a)^-1 * n%:R) * p a 0 : R^o))) => a ha.
exact: (dgpr_kernel_time_derivative 0 ha).
Qed.

(** Source for [dgpr_half_big_class_zero]: finite sums of continuous
    functions are continuous; supporting lem:heat_extension(1). *)
Lemma dgpr_half_big_class_zero (I : Type) (r : seq I) (F : I -> W -> R) :
  (forall i, norm_class_zero NW A1 dgpr_positive_time (fun w => (F i w : R^o))) ->
  norm_class_zero NW A1 dgpr_positive_time (fun w => (\sum_(i <- r) F i w : R^o)).
Proof.
move=> hF; elim: r => [|i r IH].
  apply: (dgpr_class_zero_ext _ (dgpr_half_constant_class_zero 0)) => w.
  by rewrite big_nil.
apply: (dgpr_class_zero_ext _ (norm_class_zero_add hA (hF i) IH)) => w.
by rewrite big_cons.
Qed.

(** Source for [dgpr_kernel_split]: p_s(z) = p_s(0) exp(-|z|^2/(4s));
    blueprint def:heat. *)
Lemma dgpr_kernel_split (s : R) (z : X) :
  p s z = p s 0 * exp ((- 4^-1) * ((\sum_i z i * z i) * s^-1)).
Proof.
rewrite /dgpr_heat_kernel (inner_norm0 (@euclidean_inner_productP R n)) expr0n /= oppr0 mul0r.
rewrite (real_exponential_zero (@RealExponential.laws R)) mulr1.
congr (_ * exp _).
rewrite (inner_norm_sqr (@euclidean_inner_productP R n) z) /euclidean_inner_product invfM.
by rewrite mulNr mulrC; ring.
Qed.

(** Source for [dgpr_kernel_family_joint_class_zero]: every member q of
    the kernel family gives a continuous function [(s,x) |-> q(s, x - y)]
    on (0,infinity) x R^n, for every y in R^n; supporting
    lem:heat_extension(1). *)
Lemma dgpr_kernel_family_joint_class_zero (q : R -> X -> R) : @dgpr_kernel_family R n q ->
  forall y : X, norm_class_zero NW A1 dgpr_positive_time
    (fun w : W => (q (w ord0) (dgpr_space_part w - y) : R^o)).
Proof.
have hcoord (i : 'I_n) (y : X) : norm_class_zero NW A1 dgpr_positive_time
    (fun w : W => ((dgpr_space_part w - y) i : R^o)).
  apply: (dgpr_class_zero_ext _ (norm_class_zero_subtract hA (dgpr_half_coordinate_class_zero (lift ord0 i))
    (dgpr_half_constant_class_zero (y i)))) => w.
  by rewrite !ffunE.
elim => [|i q' hq IH|q' hq IH|q1 q2 h1 IH1 h2 IH2|c q' hq IH] y.
- have hsum := dgpr_half_big_class_zero (index_enum 'I_n)
    (fun i => norm_class_zero_scalar_product hA (hcoord i y) (hcoord i y)).
  have hrec := dgpr_time_compose_class_zero dgpr_reciprocal_class_zero.
  have harg := norm_class_zero_scale hA (- 4^-1) (norm_class_zero_scalar_product hA hsum hrec).
  have hexp := dgpr_whole_compose_class_zero dgpr_exponential_class_zero harg.
  have hor := dgpr_time_compose_class_zero dgpr_kernel_origin_class_zero.
  apply: (dgpr_class_zero_ext _ (norm_class_zero_scalar_product hA hor hexp)) => w /=.
  by rewrite [in RHS]dgpr_kernel_split.
- apply: (dgpr_class_zero_ext _ (norm_class_zero_scalar_product hA (hcoord i y) (IH y))) => w.
  by [].
- have hrec := dgpr_time_compose_class_zero dgpr_reciprocal_class_zero.
  apply: (dgpr_class_zero_ext _ (norm_class_zero_scalar_product hA hrec (IH y))) => w.
  by [].
- apply: (dgpr_class_zero_ext _ (norm_class_zero_add hA (IH1 y) (IH2 y))) => w.
  by [].
- apply: (dgpr_class_zero_ext _ (norm_class_zero_scale hA c (IH y))) => w.
  by [].
Qed.
End JointContinuity.
