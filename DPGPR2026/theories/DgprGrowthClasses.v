(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    dgpr_blueprint.tex, section 3, def:classes: maps of polynomial growth
    and of Gaussian decay on R^n and before T on Omega_T, and locally
    Lipschitzian maps of polynomial growth.

    The jth differential D^j f(x) is Federer's higher differential of
    3.1.11 with values in the space of continuous j linear maps and its
    norm; class infinity is Federer's class of 3.1.11. The space
    R x R^n carries the product inner product of Federer 1.7.11. The
    file also proves the scalar inequalities between the weights
    c (1 + r)^c and c exp(-r^2/c) used for the closure properties of
    lem:classes. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets lra ring.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm HilbertFormCompactness ScalarInnerProduct ProductInner
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  NormRegularity RealExponentialUP RealExponentialSealed RealExponentialLaws RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Weights.
Variable R : realType.
Local Notation E := (@RealExponential.exponential R).
Local Notation L := (@RealExponential.logarithm R).
Local Notation h := (@RealExponential.laws R).

(** Source for [dgpr_polynomial_weight]: the bound c (1 + |x|)^c of
    def:classes, blueprint section 3, as a function of r = |x|. *)
Definition dgpr_polynomial_weight (c r : R) := c * real_power (1 + r) c.

(** Source for [dgpr_gaussian_weight]: the bound c exp(-|x|^2/c) of
    def:classes, blueprint section 3, as a function of r = |x|. *)
Definition dgpr_gaussian_weight (c r : R) := c * E (- r ^+ 2 / c).

(** Source for [dgpr_polynomial_weightE]: the power (1 + r)^c equals
    exp(c log(1 + r)), Federer 2.4.12, p. 86; supporting def:classes. *)
Lemma dgpr_polynomial_weightE (c r : R) : 0 <= r ->
  dgpr_polynomial_weight c r = c * E (c * L (1 + r)).
Proof. by move=> hr; rewrite /dgpr_polynomial_weight real_power_positive_base //; lra. Qed.

(** Source for [dgpr_log_one_plus_nonnegative]: log(1 + r) >= 0 for
    r >= 0; supporting lem:classes. *)
Lemma dgpr_log_one_plus_nonnegative (r : R) : 0 <= r -> 0 <= L (1 + r).
Proof. by move=> hr; rewrite -(real_logarithm_one R) real_logarithm_order //; lra. Qed.

(** Source for [dgpr_log_one_plus_le]: log(1 + r) <= r for r >= 0;
    supporting lem:classes. *)
Lemma dgpr_log_one_plus_le (r : R) : 0 <= r -> L (1 + r) <= r.
Proof.
move=> hr; have h1 := @real_logarithm_tangent R (1 + r).
have : L (1 + r) <= 1 + r - 1 by apply: h1; lra.
lra.
Qed.

(** Source for [dgpr_exponential_positive]: exp(x) > 0; supporting
    def:classes. *)
Lemma dgpr_exponential_positive (x : R) : 0 < E x.
Proof. exact: (real_exponential_positive h). Qed.

(** Source for [dgpr_polynomial_weight_nonnegative]: c (1 + r)^c >= 0
    for c >= 0; supporting def:classes. *)
Lemma dgpr_polynomial_weight_nonnegative (c r : R) : 0 <= c ->
  0 <= dgpr_polynomial_weight c r.
Proof.
move=> hc; rewrite /dgpr_polynomial_weight; apply: mulr_ge0 hc _.
exact: real_power_nonnegative.
Qed.

(** Source for [dgpr_gaussian_weight_nonnegative]: c exp(-r^2/c) >= 0
    for c >= 0; supporting def:classes. *)
Lemma dgpr_gaussian_weight_nonnegative (c r : R) : 0 <= c ->
  0 <= dgpr_gaussian_weight c r.
Proof.
move=> hc; rewrite /dgpr_gaussian_weight; apply: mulr_ge0 hc _.
exact: ltW (dgpr_exponential_positive _).
Qed.

(** Source for [dgpr_polynomial_weight_product]: a constant multiple of
    a product of two polynomial weights is bounded by a polynomial
    weight; proof of lem:classes (cl:product), blueprint section 3. *)
Lemma dgpr_polynomial_weight_product (b c1 c2 r : R) :
  0 <= b -> 0 < c1 -> 0 < c2 -> 0 <= r ->
  b * (dgpr_polynomial_weight c1 r * dgpr_polynomial_weight c2 r) <=
    dgpr_polynomial_weight (b * c1 * c2 + c1 + c2) r.
Proof.
move=> hb h1 h2 hr; rewrite !dgpr_polynomial_weightE //.
have hL := dgpr_log_one_plus_nonnegative hr.
set l := L (1 + r).
have hbcc : 0 <= b * c1 * c2 by apply: mulr_ge0; [apply: mulr_ge0|]; lra.
have he : E (c1 * l) * E (c2 * l) = E ((c1 + c2) * l).
  by rewrite -(real_exponential_add h) mulrDl.
have hmon : E ((c1 + c2) * l) <= E ((b * c1 * c2 + c1 + c2) * l).
  rewrite real_exponential_order.
  have hle : c1 + c2 <= b * c1 * c2 + c1 + c2 by lra.
  exact: (ler_wpM2r hL hle).
have hpos := dgpr_exponential_positive ((c1 + c2) * l).
have -> : b * (c1 * E (c1 * l) * (c2 * E (c2 * l))) =
    (b * c1 * c2) * E ((c1 + c2) * l) by rewrite -he; ring.
have hc : b * c1 * c2 <= b * c1 * c2 + c1 + c2 by lra.
apply: le_trans (ler_wpM2r (ltW hpos) hc) _.
have hc3 : 0 <= b * c1 * c2 + c1 + c2 by lra.
exact: (ler_wpM2l hc3 hmon).
Qed.

(** Source for [dgpr_polynomial_weight_sum]: the sum of two polynomial
    weights is a polynomial weight; proof of lem:classes. *)
Lemma dgpr_polynomial_weight_sum (c1 c2 r : R) :
  0 < c1 -> 0 < c2 -> 0 <= r ->
  dgpr_polynomial_weight c1 r + dgpr_polynomial_weight c2 r <=
    dgpr_polynomial_weight (c1 + c2) r.
Proof.
move=> h1 h2 hr; rewrite !dgpr_polynomial_weightE //.
have hL := dgpr_log_one_plus_nonnegative hr.
set l := L (1 + r).
have hm1 : E (c1 * l) <= E ((c1 + c2) * l).
  rewrite real_exponential_order; have hle : c1 <= c1 + c2 by lra.
  exact: (ler_wpM2r hL hle).
have hm2 : E (c2 * l) <= E ((c1 + c2) * l).
  rewrite real_exponential_order; have hle : c2 <= c1 + c2 by lra.
  exact: (ler_wpM2r hL hle).
rewrite mulrDl; apply: lerD.
- exact: (ler_wpM2l (ltW h1) hm1).
- exact: (ler_wpM2l (ltW h2) hm2).
Qed.

(** Source for [dgpr_polynomial_weight_monotone]: the polynomial weight
    increases with r; supporting def:classes. *)
Lemma dgpr_polynomial_weight_monotone (c r s : R) :
  0 <= c -> 0 <= r -> r <= s ->
  dgpr_polynomial_weight c r <= dgpr_polynomial_weight c s.
Proof.
move=> hc hr hrs; rewrite !dgpr_polynomial_weightE //; last lra.
apply: (ler_wpM2l hc); rewrite real_exponential_order.
apply: (ler_wpM2l hc); rewrite real_logarithm_order //; lra.
Qed.

(** Source for [dgpr_polynomial_weight_constant]: the polynomial weight
    increases with c; supporting def:classes. *)
Lemma dgpr_polynomial_weight_constant (c c' r : R) :
  0 <= c -> c <= c' -> 0 <= r ->
  dgpr_polynomial_weight c r <= dgpr_polynomial_weight c' r.
Proof.
move=> hc hcc hr; rewrite !dgpr_polynomial_weightE //.
have hL := dgpr_log_one_plus_nonnegative hr.
have hm : E (c * L (1 + r)) <= E (c' * L (1 + r)).
  by rewrite real_exponential_order; exact: (ler_wpM2r hL hcc).
apply: le_trans (ler_wpM2l hc hm) _.
exact: (ler_wpM2r (ltW (dgpr_exponential_positive _)) hcc).
Qed.

(** Source for [dgpr_polynomial_weight_one]: (1 + r)^c >= 1 for
    c, r >= 0; supporting def:classes. *)
Lemma dgpr_polynomial_weight_one (c r : R) : 0 <= c -> 0 <= r ->
  c <= dgpr_polynomial_weight c r.
Proof.
move=> hc hr; rewrite dgpr_polynomial_weightE //.
have hL := dgpr_log_one_plus_nonnegative hr.
have h1 : 1 <= E (c * L (1 + r)).
  rewrite -[X in X <= _](real_exponential_zero h) real_exponential_order.
  exact: (mulr_ge0 hc hL).
by rewrite -{1}[c]mulr1; exact: (ler_wpM2l hc h1).
Qed.

(** Source for [dgpr_gaussian_exponent_monotone]: -r^2/c increases with
    c; supporting lem:classes. *)
Lemma dgpr_gaussian_exponent_monotone (c c' r : R) :
  0 < c -> c <= c' -> - r ^+ 2 / c <= - r ^+ 2 / c'.
Proof.
move=> hc hcc; rewrite !mulNr lerN2.
have hinv : c'^-1 <= c^-1.
  by rewrite lef_pV2 ?posrE //; apply: lt_le_trans hcc.
exact: (ler_wpM2l (sqr_ge0 r) hinv).
Qed.

(** Source for [dgpr_gaussian_weight_constant]: the Gaussian weight
    increases with c; supporting def:classes. *)
Lemma dgpr_gaussian_weight_constant (c c' r : R) :
  0 < c -> c <= c' -> dgpr_gaussian_weight c r <= dgpr_gaussian_weight c' r.
Proof.
move=> hc hcc; rewrite /dgpr_gaussian_weight.
have hm : E (- r ^+ 2 / c) <= E (- r ^+ 2 / c').
  by rewrite real_exponential_order; exact: dgpr_gaussian_exponent_monotone.
apply: le_trans (ler_wpM2l (ltW hc) hm) _.
exact: (ler_wpM2r (ltW (dgpr_exponential_positive _)) hcc).
Qed.

(** Source for [dgpr_gaussian_weight_sum]: the sum of two Gaussian
    weights is a Gaussian weight; proof of lem:classes. *)
Lemma dgpr_gaussian_weight_sum (c1 c2 r : R) :
  0 < c1 -> 0 < c2 ->
  dgpr_gaussian_weight c1 r + dgpr_gaussian_weight c2 r <=
    dgpr_gaussian_weight (c1 + c2) r.
Proof.
move=> h1 h2; rewrite /dgpr_gaussian_weight mulrDl; apply: lerD.
- have hle : E (- r ^+ 2 / c1) <= E (- r ^+ 2 / (c1 + c2)).
    by rewrite real_exponential_order; apply: dgpr_gaussian_exponent_monotone; lra.
  exact: (ler_wpM2l (ltW h1) hle).
- have hle : E (- r ^+ 2 / c2) <= E (- r ^+ 2 / (c1 + c2)).
    by rewrite real_exponential_order; apply: dgpr_gaussian_exponent_monotone; lra.
  exact: (ler_wpM2l (ltW h2) hle).
Qed.

(** Source for [dgpr_polynomial_gaussian_constant]: the constant c'' of
    the inequality (1 + |x|)^c exp(-|x|^2/c') <= c'' exp(-|x|^2/c'')
    in the proof of lem:classes, blueprint section 3. *)
Definition dgpr_polynomial_gaussian_constant (b c1 c2 : R) :=
  b * c1 * c2 * E (c2 * c1 ^+ 2 / 2) + 2 * c2.

(** Source for [dgpr_polynomial_gaussian_constant_positive]: the
    constant c'' is positive; supporting lem:classes. *)
Lemma dgpr_polynomial_gaussian_constant_positive (b c1 c2 : R) :
  0 <= b -> 0 < c1 -> 0 < c2 -> 0 < dgpr_polynomial_gaussian_constant b c1 c2.
Proof.
move=> hb h1 h2; rewrite /dgpr_polynomial_gaussian_constant.
have hK := dgpr_exponential_positive (c2 * c1 ^+ 2 / 2).
have : 0 <= b * c1 * c2 * E (c2 * c1 ^+ 2 / 2).
  by apply: mulr_ge0; [apply: mulr_ge0; [apply: mulr_ge0|]|]; lra.
lra.
Qed.

(** Source for [dgpr_polynomial_gaussian_weight_product]: a constant
    multiple of a polynomial weight times a Gaussian weight is bounded by
    a Gaussian weight; the inequality
    (1 + |x|)^c exp(-|x|^2/c') <= c'' exp(-|x|^2/c'') in the proof of
    lem:classes (cl:product), blueprint section 3. *)
Lemma dgpr_polynomial_gaussian_weight_product (b c1 c2 r : R) :
  0 <= b -> 0 < c1 -> 0 < c2 -> 0 <= r ->
  b * (dgpr_polynomial_weight c1 r * dgpr_gaussian_weight c2 r) <=
    dgpr_gaussian_weight (dgpr_polynomial_gaussian_constant b c1 c2) r.
Proof.
move=> hb h1 h2 hr.
rewrite dgpr_polynomial_weightE // /dgpr_gaussian_weight /dgpr_polynomial_gaussian_constant.
set K := E (c2 * c1 ^+ 2 / 2).
have hK : 0 < K := dgpr_exponential_positive _.
have hbcc : 0 <= b * c1 * c2 * K.
  by apply: mulr_ge0; [apply: mulr_ge0; [apply: mulr_ge0|]|]; lra.
set c3 := b * c1 * c2 * K + 2 * c2.
have hc3 : 2 * c2 <= c3 by rewrite /c3; lra.
have hlog := dgpr_log_one_plus_le hr.
have hamgm : c1 * r <= r ^+ 2 / (2 * c2) + c2 * c1 ^+ 2 / 2.
  have hsq : 0 <= (r - c2 * c1) ^+ 2 / (2 * c2).
    by apply: divr_ge0; [exact: sqr_ge0|lra].
  have he : (r - c2 * c1) ^+ 2 / (2 * c2) =
      r ^+ 2 / (2 * c2) + c2 * c1 ^+ 2 / 2 - c1 * r.
    by field; lra.
  lra.
have hexp : c1 * L (1 + r) + - r ^+ 2 / c2 <= c2 * c1 ^+ 2 / 2 + - r ^+ 2 / c3.
  have h3 : - r ^+ 2 / (2 * c2) <= - r ^+ 2 / c3.
    by apply: dgpr_gaussian_exponent_monotone; lra.
  have h4 : c1 * L (1 + r) <= c1 * r by exact: (ler_wpM2l (ltW h1) hlog).
  have he : - r ^+ 2 / c2 = - r ^+ 2 / (2 * c2) - r ^+ 2 / (2 * c2).
    by field; lra.
  rewrite he; lra.
have hE : E (c1 * L (1 + r)) * E (- r ^+ 2 / c2) <= K * E (- r ^+ 2 / c3).
  by rewrite -!(real_exponential_add h) real_exponential_order.
have -> : b * (c1 * E (c1 * L (1 + r)) * (c2 * E (- r ^+ 2 / c2))) =
    (b * c1 * c2) * (E (c1 * L (1 + r)) * E (- r ^+ 2 / c2)) by ring.
have hbc : 0 <= b * c1 * c2 by apply: mulr_ge0; [apply: mulr_ge0|]; lra.
apply: le_trans (ler_wpM2l hbc hE) _.
rewrite mulrA.
have hle : b * c1 * c2 * K <= c3 by rewrite /c3; lra.
exact: (ler_wpM2r (ltW (dgpr_exponential_positive _)) hle).
Qed.

(** Source for [dgpr_gaussian_polynomial_weight]: exp(-r^2/c) <= 1 <=
    (1 + r)^c, so that Gaussian decay implies polynomial growth;
    supporting def:classes. *)
Lemma dgpr_gaussian_polynomial_weight (c r : R) :
  0 < c -> 0 <= r -> dgpr_gaussian_weight c r <= dgpr_polynomial_weight c r.
Proof.
move=> hc hr; rewrite dgpr_polynomial_weightE // /dgpr_gaussian_weight.
have hle : E (- r ^+ 2 / c) <= E (c * L (1 + r)).
  rewrite real_exponential_order.
  have hL := dgpr_log_one_plus_nonnegative hr.
  have : 0 <= c * L (1 + r) by apply: mulr_ge0; lra.
  have : 0 <= r ^+ 2 / c by apply: divr_ge0; [exact: sqr_ge0|lra].
  rewrite mulNr; lra.
exact: (ler_wpM2l (ltW hc) hle).
Qed.
End Weights.

Section HigherDifferentials.
Variable R : realType.
Variables (X Y : lmodType R) (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.

(** Source for [dgpr_higher_differential]: the relation D^j f(x) = z of
    mr:notation, blueprint section 2, for the jth differential of
    Federer 3.1.11, p. 219, with values in the space of continuous
    j linear maps of X into Y. The domain A of f is open in all uses. *)
Definition dgpr_higher_differential (A : set X) (f : X->Y) (j : nat) (x : X)
    (z : @ContinuousMultilinear.space R j X Y NX NY hNX hNY) : Prop :=
  has_norm_higher_differential NX
    (fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY)
    (fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY) A f j x z.

(** Source for [dgpr_derivative_bounded]: the estimate ||D^j f(x)|| <= w(x)
    for x in S, where ||.|| is the norm of Federer 3.1.11, p. 219,
    corrected by the erratum, book p. 219 line 4; def:classes. *)
Definition dgpr_derivative_bounded (A S : set X) (f : X->Y) (j : nat) (w : X->R) :=
  forall x z, S x -> @dgpr_higher_differential A f j x z ->
    @ContinuousMultilinear.norm R j X Y NX NY hNX hNY z <= w x.
End HigherDifferentials.

Arguments dgpr_higher_differential {R X Y NX NY} hNX hNY A f j x z.
Arguments dgpr_derivative_bounded {R X Y NX NY} hNX hNY A S f j w.

Section Classes.
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
Variables (Z : lmodType R) (NZ : Z->R).
Hypothesis hNZ : is_real_norm NZ.

(** Source for [dgpr_polynomial_growth]: def:classes, blueprint section 3,
    first paragraph: f is of class infinity on R^n and for each j there
    is 0 < c < infinity with ||D^j f(x)|| <= c (1 + |x|)^c. *)
Definition dgpr_polynomial_growth (f : X->Z) :=
  norm_class_all_orders hNX hNZ setT f /\
  forall j, exists c, 0 < c /\
    dgpr_derivative_bounded hNX hNZ setT setT f j
      (fun x=>dgpr_polynomial_weight c (NX x)).

(** Source for [dgpr_gaussian_decay]: def:classes, blueprint section 3,
    first paragraph: f is of class infinity on R^n and for each j there
    is 0 < c < infinity with ||D^j f(x)|| <= c exp(-|x|^2/c). *)
Definition dgpr_gaussian_decay (f : X->Z) :=
  norm_class_all_orders hNX hNZ setT f /\
  forall j, exists c, 0 < c /\
    dgpr_derivative_bounded hNX hNZ setT setT f j
      (fun x=>dgpr_gaussian_weight c (NX x)).

(** Source for [dgpr_before]: the set Omega_T of (t,x) in R x R^n with
    t < T, mr:notation, blueprint section 2. *)
Definition dgpr_before (T : R) : set TX := [set p | p.1 < T].

(** Source for [dgpr_time_strip]: the points (t,x) with t in the compact
    interval J = [a,b]; def:classes, second paragraph. *)
Definition dgpr_time_strip (a b : R) : set TX := [set p | a <= p.1 <= b].

(** Source for [dgpr_polynomial_growth_before]: def:classes, blueprint
    section 3, second paragraph: f is of class infinity on Omega_T, and
    for each j and each compact interval J = [a,b] with b < T there is
    0 < c < infinity with ||D^j f(t,x)|| <= c (1 + |x|)^c for t in J and
    x in R^n. The differential is taken with respect to (t,x). *)
Definition dgpr_polynomial_growth_before (T : R) (f : TX->Z) :=
  norm_class_all_orders hNT hNZ (dgpr_before T) f /\
  forall j (a b : R), b < T -> exists c, 0 < c /\
    dgpr_derivative_bounded hNT hNZ (dgpr_before T) (dgpr_time_strip a b) f j
      (fun p=>dgpr_polynomial_weight c (NX p.2)).

(** Source for [dgpr_gaussian_decay_before]: def:classes, blueprint
    section 3, second paragraph, with c exp(-|x|^2/c) in place of
    c (1 + |x|)^c. *)
Definition dgpr_gaussian_decay_before (T : R) (f : TX->Z) :=
  norm_class_all_orders hNT hNZ (dgpr_before T) f /\
  forall j (a b : R), b < T -> exists c, 0 < c /\
    dgpr_derivative_bounded hNT hNZ (dgpr_before T) (dgpr_time_strip a b) f j
      (fun p=>dgpr_gaussian_weight c (NX p.2)).

(** Source for [dgpr_gaussian_decay_polynomial_growth]: Gaussian decay
    implies polynomial growth, since exp(-|x|^2/c) <= (1 + |x|)^c;
    supporting def:classes. *)
Lemma dgpr_gaussian_decay_polynomial_growth (f : X->Z) :
  dgpr_gaussian_decay f -> dgpr_polynomial_growth f.
Proof.
move=> [hf hb]; split=> // j; have [c [hc hj]] := hb j.
exists c; split=> // x z hx hz; apply: le_trans (hj x z hx hz) _.
exact: dgpr_gaussian_polynomial_weight hc (inner_norm_nonnegative _ _).
Qed.

(** Source for [dgpr_gaussian_decay_before_polynomial_growth_before]:
    Gaussian decay before T implies polynomial growth before T;
    supporting def:classes. *)
Lemma dgpr_gaussian_decay_before_polynomial_growth_before (T : R) (f : TX->Z) :
  dgpr_gaussian_decay_before T f -> dgpr_polynomial_growth_before T f.
Proof.
move=> [hf hb]; split=> // j a b hbT; have [c [hc hj]] := hb j a b hbT.
exists c; split=> // p z hp hz; apply: le_trans (hj p z hp hz) _.
exact: dgpr_gaussian_polynomial_weight hc (inner_norm_nonnegative _ _).
Qed.

(** Source for [dgpr_lipschitz_polynomial_growth]: def:classes,
    blueprint section 3, third paragraph: e is locally Lipschitzian and
    there is 0 < c < infinity with |e(x)| + Lip(e | B(x,1)) <= c (1 + |x|)^c
    for x in R^n. The bound on Lip(e | B(x,1)) is expressed by a number
    L >= 0 with |e(y) - e(z)| <= L |y - z| for y, z in B(x,1). *)
Definition dgpr_lipschitz_polynomial_growth (e : X->X) :=
  exists c, 0 < c /\ forall x, exists L, 0 <= L /\
    NX (e x) + L <= dgpr_polynomial_weight c (NX x) /\
    forall y z, NX (y - x) <= 1 -> NX (z - x) <= 1 ->
      NX (e y - e z) <= L * NX (y - z).
End Classes.
