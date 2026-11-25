(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3, proof
    of Lemma 3.1 (the identities for the heat operators H and H_zeta of
    (3.6)); blueprint dgpr_blueprint.tex, proof of lem:heat_calculus. The
    file proves the calculus of the second order jets of DgprHeatJets.v:
    jets of sums, constant multiples, linear images, products of a real
    function with a vector valued one, squared norms for an inner product,
    and compositions [q |-> Phi(phi(q))] with a real function Phi of class 2
    on (0,infinity). From these follow the generic forms of the identities
    lem:heat_calculus(product), (square) and (chain), and the product rule
    for H used in lem:heat_calculus(S). The derivatives are those of
    Federer 2.9.22 (curves) and 3.1.1 (differentials); the rules are the
    Leibniz formula and the chain rule of Federer 3.1.11. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra ring.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerNorm InnerNormInequalities HilbertFormCompactness FiniteCoordinates CoordinateProjection TensorUP
  Bilinear NormBoundedBilinearUP NormDifferentialUP NormDifferentialArithmetic NormDifferentialScalar
  NormDifferentialScalarProduct NormBilinearDifferentialAlgebra NormDifferentialBilinearProduct
  NormDifferentialChain NormedCurveDerivativeUP NormedCurveLinearMap RealCurveDerivativeUP
  RealCurveDerivativeLaws RealCurveDerivativeAlgebra NormHigherCurveDerivativeUP RealCurvePolynomialDerivatives
  ScalarReciprocalDifferential RealLogarithmDifferential RealExponentialUP RealExponentialSealed.
From DPGPR Require Import DgprDifferentialCalculus DgprHeatJets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section CurveBridge.
Variable R : realType.
Local Notation A1 := (fun t : R^o => `|t|).

(** Source for [dgpr_real_interior_setT]: every point of R is an interior
    point of R (Federer 3.1.1, p. 209, opening definition). *)
Lemma dgpr_real_interior_setT (a : R) : norm_domain_interior A1 setT a.
Proof. by exists 1; split => //; exact: ltr01. Qed.

Variables (Z : lmodType R) (NZ : Z -> R).
Hypothesis hNZ : is_real_norm NZ.

(** Source for [dgpr_curve_to_differential]: Federer 3.1.1, p. 209, first
    special case: a curve derivative a at t gives the differential
    [h |-> h a] at t. *)
Lemma dgpr_curve_to_differential (g : R -> Z) (t : R) (a : Z) :
  has_normed_curve_derivative NZ g t a ->
  has_norm_differential A1 NZ setT g t (scalar_coefficient_linear_map a).
Proof.
move=> h; apply/(@norm_differential_real_source R Z NZ hNZ setT g t).
split; first exact: dgpr_real_interior_setT.
by change (has_normed_curve_derivative NZ g t (1 *: a)); rewrite scale1r.
Qed.

(** Source for [dgpr_differential_to_curve]: Federer 3.1.1, p. 209, first
    special case: a differential L at t gives the curve derivative L(1). *)
Lemma dgpr_differential_to_curve (g : R -> Z) (t : R) (L : Hom R^o Z) :
  has_norm_differential A1 NZ setT g t L -> has_normed_curve_derivative NZ g t (L 1).
Proof. by move=> h; have [_ h'] := (@norm_differential_real_source R Z NZ hNZ setT g t L).1 h. Qed.

End CurveBridge.

Section CurveCalculus.
Variable R : realType.
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Variables (Z : lmodType R) (NZ : Z -> R).
Hypothesis hNZ : is_real_norm NZ.

(** Source for [dgpr_curve_add]: Federer 2.9.22 with 3.1.1(5), p. 210:
    the derivative of a sum of curves. *)
Lemma dgpr_curve_add (f g : R -> Z) (t : R) (a b : Z) :
  has_normed_curve_derivative NZ f t a -> has_normed_curve_derivative NZ g t b ->
  has_normed_curve_derivative NZ (fun r => f r + g r) t (a + b).
Proof.
move=> hf hg.
have h := dgpr_differential_to_curve hNZ
  (norm_differential_add hNZ (dgpr_curve_to_differential hNZ hf) (dgpr_curve_to_differential hNZ hg)).
move: h; rewrite hom_addE.
by change (has_normed_curve_derivative NZ (fun r => f r + g r) t (1 *: a + 1 *: b) ->
  has_normed_curve_derivative NZ (fun r => f r + g r) t (a + b)); rewrite !scale1r.
Qed.

(** Source for [dgpr_curve_scalar_product]: Federer 2.9.22 with the
    product rule of 3.1.11, pp. 220-222: the derivative of
    [r |-> g(r) f(r)] is g'(t) f(t) + g(t) f'(t). *)
Lemma dgpr_curve_scalar_product (g : R -> R) (f : R -> Z) (t : R) (ag : R) (af : Z) :
  has_real_curve_derivative g t ag -> has_normed_curve_derivative NZ f t af ->
  has_normed_curve_derivative NZ (fun r => g r *: f r) t (ag *: f t + g t *: af).
Proof.
move=> hg hf.
have hg' := dgpr_curve_to_differential hA (proj2 (scalar_normed_curve_derivative g t ag) hg).
have h := dgpr_differential_to_curve hNZ
  (norm_differential_scalar_product hA hNZ hg' (dgpr_curve_to_differential hNZ hf)).
move: h; rewrite /scalar_vector_product_linear_term hom_addE hom_compE hom_scaleE.
by change (has_normed_curve_derivative NZ (fun r => g r *: f r) t ((1 * ag) *: f t + g t *: (1 *: af)) ->
  has_normed_curve_derivative NZ (fun r => g r *: f r) t (ag *: f t + g t *: af));
  rewrite mul1r scale1r.
Qed.

(** Source for [dgpr_real_curve_constant]: the derivative of a constant
    real function is 0 (Federer 2.9.19). *)
Lemma dgpr_real_curve_constant (c t : R) : has_real_curve_derivative (fun _ => c) t 0.
Proof.
apply: (@punctured_real_limit_congr R (fun _ => 0)); last exact: punctured_real_constant_limit.
by move=> h _; rewrite subrr mul0r.
Qed.

(** Source for [dgpr_curve_scale]: Federer 2.9.22: the derivative of
    [r |-> c f(r)] for a constant c is c f'(t). *)
Lemma dgpr_curve_scale (c : R) (f : R -> Z) (t : R) (a : Z) :
  has_normed_curve_derivative NZ f t a -> has_normed_curve_derivative NZ (fun r => c *: f r) t (c *: a).
Proof.
move=> hf; have h := dgpr_curve_scalar_product (dgpr_real_curve_constant c t) hf.
by rewrite scale0r add0r in h.
Qed.

End CurveCalculus.

Section CurveInner.
Variable R : realType.
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Variables (Z : lmodType R) (CZ : Z -> Z -> R).
Hypothesis hCZ : is_inner_product CZ.
Local Notation NZ := (inner_norm hCZ).
Local Notation hNZ := (inner_norm_real_norm hCZ).

(** Source for [dgpr_inner_bound]: the Cauchy inequality
    |CZ(u,v)| <= |u| |v| (Federer 1.7.1), in the form of a bound of the
    bilinear map CZ. *)
Lemma dgpr_inner_bound (u v : Z) : A1 (CZ u v) <= 1 * (NZ u * NZ v).
Proof. by rewrite mul1r; exact: (inner_cauchy hCZ). Qed.

(** Source for [dgpr_curve_inner_square]: Federer 2.9.22 with the
    product rule of 3.1.11, p. 220, for the bilinear map CZ: the
    derivative of [r |-> CZ(f(r), f(r))] is 2 CZ(f(t), f'(t)). *)
Lemma dgpr_curve_inner_square (f : R -> Z) (t : R) (a : Z) :
  has_normed_curve_derivative NZ f t a ->
  has_real_curve_derivative (fun r => CZ (f r) (f r)) t (2 * CZ (f t) a).
Proof.
move=> hf; have hd := dgpr_curve_to_differential hNZ hf.
have h := dgpr_differential_to_curve hA
  (norm_differential_bilinear_product hA hNZ hNZ hA (inner_bilinear hCZ) ler01 dgpr_inner_bound hd hd).
apply/scalar_normed_curve_derivative.
move: h; change (has_normed_curve_derivative A1 (fun r => CZ (f r) (f r)) t
  (CZ (1 *: a) (f t) + CZ (f t) (1 *: a)) ->
  has_normed_curve_derivative A1 (fun r => CZ (f r) (f r)) t (2 * CZ (f t) a)).
by rewrite scale1r (inner_symmetric hCZ a) mulr2n mulrDl mul1r.
Qed.

End CurveInner.

Section RealCurves.
Variable R : realType.
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).

(** Source for [dgpr_real_curve_chain]: the chain rule for real
    functions of one real variable (Federer 3.1.1(3), p. 210, in
    dimension 1): the derivative of [r |-> Phi(phi(r))] at t is
    Phi'(phi(t)) phi'(t). *)
Lemma dgpr_real_curve_chain (Phi phi : R -> R) (t a b : R) :
  has_real_curve_derivative phi t a -> has_real_curve_derivative Phi (phi t) b ->
  has_real_curve_derivative (fun r => Phi (phi r)) t (b * a).
Proof. by rewrite mulrC; exact: real_curve_derivative_compose. Qed.

(** Source for [dgpr_real_curve_product]: the Leibniz rule for real
    functions of one real variable (Federer 3.1.11, pp. 220-222, in
    dimension 1). *)
Lemma dgpr_real_curve_product (g f : R -> R) (t ag af : R) :
  has_real_curve_derivative g t ag -> has_real_curve_derivative f t af ->
  has_real_curve_derivative (fun r => g r * f r) t (ag * f t + g t * af).
Proof.
move=> hg hf; apply/scalar_normed_curve_derivative.
exact: (dgpr_curve_scalar_product hA hg (proj2 (scalar_normed_curve_derivative f t af) hf)).
Qed.

(** Source for [dgpr_real_curve_reciprocal]: Federer 3.1.1, p. 209, for
    [s |-> s^-1] on R without 0: its derivative at r is -r^-2. *)
Lemma dgpr_real_curve_reciprocal (r : R) :
  r != 0 -> has_real_curve_derivative (fun s => s^-1) r (- r ^- 2).
Proof.
move=> hr; apply/scalar_normed_curve_derivative.
have [_ h] := (@norm_differential_real_source R R^o A1 hA (fun s : R^o => s != 0) (fun s => s^-1) r _).1
  (scalar_reciprocal_differential hr).
move: h; change (has_normed_curve_derivative A1 (fun s : R => s^-1) r (1 * (- (r^-1 ^+ 2))) ->
  has_normed_curve_derivative A1 (fun s : R => s^-1) r (- r ^- 2)).
by rewrite mul1r exprVn.
Qed.

(** Source for [dgpr_real_curve_inverse]: Federer 3.1.1, p. 209, for
    Phi(r) = r^-1 on (0,infinity), with Phi'(r) = -r^-2 and
    Phi''(r) = 2 r^-3; the form of the hypotheses of
    [dgpr_heat_jet_compose], used for lem:heat_calculus(chain). *)
Lemma dgpr_real_curve_inverse :
  (forall r : R, 0 < r -> has_real_curve_derivative (fun s => s^-1) r (- r ^- 2)) /\
  (forall r : R, 0 < r -> has_real_curve_derivative (fun s => - s ^- 2) r (2 * r ^- 3)).
Proof.
split=> r hr; first exact: (dgpr_real_curve_reciprocal (lt0r_neq0 hr)).
have h1 := dgpr_real_curve_reciprocal (lt0r_neq0 hr).
have h2 := dgpr_real_curve_product h1 h1.
have h3 := dgpr_curve_scale hA (-1) (proj2 (scalar_normed_curve_derivative _ r _) h2).
move/scalar_normed_curve_derivative: h3.
have -> : (fun s : R => (-1) *: (s^-1 * s^-1 : R^o)) = (fun s => - s ^- 2).
  by apply: funext => s; rewrite -exprVn expr2; change ((-1) * (s^-1 * s^-1) = - (s^-1 * s^-1)); rewrite mulN1r.
suff -> : 2 * r ^- 3 = (-1) *: ((- r ^- 2) * r^-1 + r^-1 * (- r ^- 2) : R^o) by [].
change (2 * r ^- 3 = (-1) * ((- r ^- 2) * r^-1 + r^-1 * (- r ^- 2))).
by rewrite -!exprVn; ring.
Qed.

(** Source for [dgpr_real_curve_logarithm]: Federer 3.1.1, p. 209, for
    Phi = log on (0,infinity), with Phi'(r) = r^-1 and
    Phi''(r) = -r^-2; the form of the hypotheses of
    [dgpr_heat_jet_compose], used for lem:heat_calculus(chain). *)
Lemma dgpr_real_curve_logarithm :
  (forall r : R, 0 < r -> has_real_curve_derivative (@RealExponential.logarithm R) r r^-1) /\
  (forall r : R, 0 < r -> has_real_curve_derivative (fun s => s^-1) r (- r ^- 2)).
Proof.
split=> r hr; last exact: (dgpr_real_curve_reciprocal (lt0r_neq0 hr)).
apply/scalar_normed_curve_derivative.
have h := dgpr_differential_to_curve hA (real_logarithm_differential hr).
move: h; change (has_normed_curve_derivative A1 (@RealExponential.logarithm R) r (r^-1 * 1) ->
  has_normed_curve_derivative A1 (@RealExponential.logarithm R) r r^-1).
by rewrite mulr1.
Qed.

End RealCurves.

Section ValuesCalculus.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation eps := (@coordinate_basis R n).

(** Source for [dgpr_values_scale]: Federer 3.1.1(5), p. 210: the
    differential of [x |-> c f(x)] for a constant c is c Df(a). *)
Lemma dgpr_values_scale (Z : lmodType R) (NZ : Z -> R) (hNZ : is_real_norm NZ) (c : R)
    (f : X -> Z) (a : X) (l : X -> Z) :
  dgpr_differential_values NZ f a l ->
  dgpr_differential_values NZ (fun x => c *: f x) a (fun v => c *: l v).
Proof.
move=> h; have h' := dgpr_values_scalar_product hNZ (@dgpr_values_constant R n R^o A1 hA c a) h.
by apply: (dgpr_values_ext _ _ h') => [x|v] //; rewrite scale0r add0r.
Qed.

(** Source for [dgpr_values_inner]: the product rule of Federer 3.1.11,
    p. 220, for the bilinear map CZ of an inner product space: the
    differential of [x |-> CZ(f(x), g(x))] at a is
    [v |-> CZ(Df(a)(v), g(a)) + CZ(f(a), Dg(a)(v))]. *)
Lemma dgpr_values_inner (Z : lmodType R) (CZ : Z -> Z -> R) (hCZ : is_inner_product CZ)
    (f g : X -> Z) (a : X) (l1 l2 : X -> Z) :
  dgpr_differential_values (inner_norm hCZ) f a l1 ->
  dgpr_differential_values (inner_norm hCZ) g a l2 ->
  @dgpr_differential_values R n R^o A1 (fun x => CZ (f x) (g x)) a
    (fun v => CZ (l1 v) (g a) + CZ (f a) (l2 v)).
Proof.
move=> [L [hL h1]] [M [hM h2]].
have hNZ := inner_norm_real_norm hCZ.
exists (norm_bilinear_product_linear_term (inner_bilinear hCZ) (f a) (g a) L M); split.
- exact: (norm_differential_bilinear_product hNX hNZ hNZ hA (inner_bilinear hCZ) ler01
    (dgpr_inner_bound hCZ) hL hM).
- by move=> v; change (CZ (L v) (g a) + CZ (f a) (M v) = CZ (l1 v) (g a) + CZ (f a) (l2 v));
    rewrite h1 h2.
Qed.

(** Source for [dgpr_values_compose_real]: the chain rule of
    Federer 3.1.1(3), p. 210, for a real function Phi of one real
    variable: the differential of [x |-> Phi(phi(x))] at a is
    [v |-> Phi'(phi(a)) Dphi(a)(v)]. *)
Lemma dgpr_values_compose_real (Phi : R -> R) (phi : X -> R) (a : X) (l : X -> R) (b : R) :
  @dgpr_differential_values R n R^o A1 phi a l -> has_real_curve_derivative Phi (phi a) b ->
  @dgpr_differential_values R n R^o A1 (fun x => Phi (phi x)) a (fun v => b * l v).
Proof.
move=> [L [hL hl]] hPhi.
have hM := dgpr_curve_to_differential hA (proj2 (scalar_normed_curve_derivative Phi (phi a) b) hPhi).
have h := norm_differential_chain hNX hA hA hL hM.
exists (hom_comp (@scalar_coefficient_linear_map R R^o b) L); split.
- have e : (setT : set X) = (fun x => setT x /\ @setT R^o (phi x)).
    by apply: funext => x; apply: propext.
  by rewrite e.
- move=> v; rewrite hom_compE -hl.
  by change (L v * b = b * L v); rewrite mulrC.
Qed.

(** Source for [dgpr_gradient_valuesE]: blueprint mr:notation: the
    gradient grad f(a) satisfies Df(a)(v) = grad f(a) . v
    (Federer 1.7.1, p. 28, and 3.1.1, p. 209). *)
Lemma dgpr_gradient_valuesE (f : X -> R) (a : X) (l : X -> R) (v : X) :
  @dgpr_differential_values R n R^o A1 f a l ->
  l v = euclidean_inner_product (dgpr_gradient_values l) v.
Proof.
move=> h; rewrite -(dgpr_values_linear v h) /dgpr_gradient_values.
have hE := @euclidean_inner_bilinear R n.
rewrite (big_morph (fun y => euclidean_inner_product y v) (fun y y' => bilDl hE y y' v) (bil0l hE v)).
apply: eq_bigr => i _; rewrite (bilZl hE) euclidean_inner_symmetric euclidean_inner_basis.
by change (v i * l (eps i) = l (eps i) * v i); rewrite mulrC.
Qed.

(** Source for [dgpr_values_gradient_sum]: blueprint mr:notation and
    proof of lem:heat_calculus: sum_i Dg(eps_i) Df(eps_i) = Df(grad g)
    for the standard basis eps of R^n, since grad g =
    sum_i Dg(eps_i) eps_i and Df(a) is linear (Federer 3.1.1). *)
Lemma dgpr_values_gradient_sum (Z : lmodType R) (NZ : Z -> R) (f : X -> Z) (a : X) (l : X -> Z)
    (c : X -> R) :
  dgpr_differential_values NZ f a l -> \sum_(i < n) c (eps i) *: l (eps i) = l (dgpr_gradient_values c).
Proof.
move=> [L [_ hl]]; rewrite -hl /dgpr_gradient_values linear_sum.
by apply: eq_bigr => i _; rewrite linearZ; congr (_ *: _); exact: esym (hl _).
Qed.

End ValuesCalculus.

Section JetCalculus.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Variables (t : R) (x : X).

(** Source for [dgpr_heat_jet_add]: Federer 2.9.22 and 3.1.1(5),
    p. 210: the jet of f + g at (t,x) is the sum of the jets. *)
Lemma dgpr_heat_jet_add (Z : lmodType R) (NZ : Z -> R) (hNZ : is_real_norm NZ) (f g : TX -> Z)
    (af ag : Z) (Df D2f Dg D2g : X -> X -> Z) :
  dgpr_heat_jet NZ f t x af Df D2f -> dgpr_heat_jet NZ g t x ag Dg D2g ->
  dgpr_heat_jet NZ (fun q => f q + g q) t x (af + ag) (fun y v => Df y v + Dg y v)
    (fun v w => D2f v w + D2g v w).
Proof.
move=> [hf [hDf hD2f]] [hg [hDg hD2g]]; split; [|split].
- exact: (dgpr_curve_add hNZ hf hg).
- by move=> y; exact: (dgpr_values_add hNZ (hDf y) (hDg y)).
- by move=> w; exact: (dgpr_values_add hNZ (hD2f w) (hD2g w)).
Qed.

(** Source for [dgpr_heat_jet_scale]: Federer 2.9.22 and 3.1.1(5),
    p. 210: the jet of c f at (t,x), for a constant c, is c times the
    jet of f. *)
Lemma dgpr_heat_jet_scale (Z : lmodType R) (NZ : Z -> R) (hNZ : is_real_norm NZ) (c : R)
    (f : TX -> Z) (a : Z) (Df D2 : X -> X -> Z) :
  dgpr_heat_jet NZ f t x a Df D2 ->
  dgpr_heat_jet NZ (fun q => c *: f q) t x (c *: a) (fun y v => c *: Df y v) (fun v w => c *: D2 v w).
Proof.
move=> [hf [hDf hD2]]; split; [|split].
- exact: (dgpr_curve_scale hNZ c hf).
- by move=> y; exact: (dgpr_values_scale hNZ c (hDf y)).
- by move=> w; exact: (dgpr_values_scale hNZ c (hD2 w)).
Qed.

(** Source for [dgpr_heat_jet_linear]: Federer 2.9.22 and 3.1.1(3),
    p. 210: the jet of L o f at (t,x), for a continuous linear map L, is
    the image of the jet of f under L. *)
Lemma dgpr_heat_jet_linear (Z Z' : lmodType R) (NZ : Z -> R) (NZ' : Z' -> R)
    (hNZ : is_real_norm NZ) (hNZ' : is_real_norm NZ') (L : Hom Z Z')
    (f : TX -> Z) (a : Z) (Df D2 : X -> X -> Z) :
  norm_bounded_linear NZ NZ' L -> dgpr_heat_jet NZ f t x a Df D2 ->
  dgpr_heat_jet NZ' (fun q => L (f q)) t x (L a) (fun y v => L (Df y v)) (fun v w => L (D2 v w)).
Proof.
move=> hL [hf [hDf hD2]]; split; [|split].
- exact: (normed_curve_derivative_linear_image hNZ hL hf).
- by move=> y; exact: (dgpr_values_postcompose hNZ hNZ' hL (hDf y)).
- by move=> w; exact: (dgpr_values_postcompose hNZ hNZ' hL (hD2 w)).
Qed.

(** Source for [dgpr_heat_jet_scalar_product]: the Leibniz rule of
    Federer 3.1.11, pp. 220-222, applied twice: the jet of g f at (t,x),
    for a real function g, with
    D^2(g f)(v,w) = D^2 g(v,w) f + Dg(w) Df(v) + Dg(v) Df(w) + g D^2 f(v,w). *)
Lemma dgpr_heat_jet_scalar_product (Z : lmodType R) (NZ : Z -> R) (hNZ : is_real_norm NZ)
    (g : TX -> R) (f : TX -> Z) (ag : R) (Dg D2g : X -> X -> R) (af : Z) (Df D2f : X -> X -> Z) :
  @dgpr_heat_jet R n R^o A1 g t x ag Dg D2g -> dgpr_heat_jet NZ f t x af Df D2f ->
  dgpr_heat_jet NZ (fun q => g q *: f q) t x (ag *: f (t, x) + g (t, x) *: af)
    (fun y v => Dg y v *: f (t, y) + g (t, y) *: Df y v)
    (fun v w => D2g v w *: f (t, x) + Dg x w *: Df x v + Dg x v *: Df x w + g (t, x) *: D2f v w).
Proof.
move=> [hg [hDg hD2g]] [hf [hDf hD2f]]; split; [|split].
- exact: (dgpr_curve_scalar_product hNZ (proj1 (scalar_normed_curve_derivative _ t ag) hg) hf).
- by move=> y; exact: (dgpr_values_scalar_product hNZ (hDg y) (hDf y)).
- move=> w; have h := dgpr_values_add hNZ (dgpr_values_scalar_product hNZ (hD2g w) (hDf x))
    (dgpr_values_scalar_product hNZ (hDg x) (hD2f w)).
  by apply: (dgpr_values_ext _ _ h) => [y|v] //; rewrite addrA.
Qed.

(** Source for [dgpr_heat_jet_inner_square]: the product rule of
    Federer 3.1.11, p. 220, for the bilinear map CZ, applied twice: the
    jet of |f|^2 = CZ(f, f) at (t,x), with
    D^2|f|^2(v,w) = 2 CZ(Df(v), Df(w)) + 2 CZ(f, D^2 f(v,w)). *)
Lemma dgpr_heat_jet_inner_square (Z : lmodType R) (CZ : Z -> Z -> R) (hCZ : is_inner_product CZ)
    (f : TX -> Z) (a : Z) (Df D2 : X -> X -> Z) :
  dgpr_heat_jet (inner_norm hCZ) f t x a Df D2 ->
  @dgpr_heat_jet R n R^o A1 (fun q => CZ (f q) (f q)) t x (2 * CZ (f (t, x)) a)
    (fun y v => 2 * CZ (f (t, y)) (Df y v))
    (fun v w => 2 * CZ (Df x v) (Df x w) + 2 * CZ (f (t, x)) (D2 v w)).
Proof.
move=> [hf [hDf hD2]]; split; [|split].
- apply/scalar_normed_curve_derivative; exact: (dgpr_curve_inner_square hf).
- move=> y; have h := dgpr_values_inner (hDf y) (hDf y).
  apply: (dgpr_values_ext _ _ h) => [z|v] //.
  by rewrite (inner_symmetric hCZ (Df y v)) mulr2n mulrDl mul1r.
- move=> w; have h := dgpr_values_scale hA 2 (dgpr_values_inner (hDf x) (hD2 w)).
  apply: (dgpr_values_ext _ _ h) => [z|v] //.
  by change (2 * (CZ (Df x v) (Df x w) + CZ (f (t, x)) (D2 v w)) =
    2 * CZ (Df x v) (Df x w) + 2 * CZ (f (t, x)) (D2 v w)); rewrite mulrDr.
Qed.

(** Source for [dgpr_heat_jet_compose]: the chain rule of Federer 3.1.1(3),
    p. 210, and the Leibniz rule of 3.1.11, p. 220: the jet of Phi o phi
    at (t,x), for a positive real function phi and a real function Phi with
    derivatives Phi1 and Phi2 = Phi1' on (0,infinity), with
    D^2(Phi o phi)(v,w) = Phi2(phi) Dphi(v) Dphi(w) + Phi1(phi) D^2 phi(v,w). *)
Lemma dgpr_heat_jet_compose (Phi Phi1 Phi2 : R -> R) (phi : TX -> R) (a : R) (Dphi D2 : X -> X -> R) :
  (forall r, 0 < r -> has_real_curve_derivative Phi r (Phi1 r)) ->
  (forall r, 0 < r -> has_real_curve_derivative Phi1 r (Phi2 r)) ->
  (forall y, 0 < phi (t, y)) ->
  @dgpr_heat_jet R n R^o A1 phi t x a Dphi D2 ->
  @dgpr_heat_jet R n R^o A1 (fun q => Phi (phi q)) t x (Phi1 (phi (t, x)) * a)
    (fun y v => Phi1 (phi (t, y)) * Dphi y v)
    (fun v w => Phi2 (phi (t, x)) * Dphi x v * Dphi x w + Phi1 (phi (t, x)) * D2 v w).
Proof.
move=> hPhi hPhi1 hpos [hphi [hD hD2]]; split; [|split].
- apply/scalar_normed_curve_derivative.
  exact: (dgpr_real_curve_chain (proj1 (scalar_normed_curve_derivative _ t a) hphi) (hPhi _ (hpos x))).
- by move=> y; exact: (dgpr_values_compose_real (hD y) (hPhi _ (hpos y))).
- move=> w; have h := dgpr_values_scalar_product hA (dgpr_values_compose_real (hD x) (hPhi1 _ (hpos x)))
    (hD2 w).
  by apply: (dgpr_values_ext _ _ h) => [y|v] //.
Qed.

End JetCalculus.

Section Identities.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation eps := (@coordinate_basis R n).
Variables (t : R) (x : X).

(** Source for [dgpr_heat_product_algebra]: the rearrangement of terms
    in the proof of lem:heat_calculus(product), in a vector space over R. *)
Lemma dgpr_heat_product_algebra (V : lmodType R) (ag sg G : R) (F af sf P : V) :
  (ag + sg) *: F + G *: (af + sf) + 2 *: P = ag *: F + G *: af + (sg *: F + P + P + G *: sf).
Proof.
rewrite scalerDl scalerDr scaler_nat mulr2n -!addrA; congr (_ + _).
rewrite addrCA; congr (_ + (_ + _)).
by rewrite addrC -addrA.
Qed.

(** Source for [dgpr_drift_product_algebra]: the rearrangement of terms
    in the proof of lem:heat_calculus(product) for H_zeta, in a vector
    space over R. *)
Lemma dgpr_drift_product_algebra (V : lmodType R) (ag sg gz G : R) (F af sf dz P : V) :
  G *: (af + sf + 2 *: dz) + (ag + sg + 2 * gz) *: F + 2 *: P =
  ag *: F + G *: af + (sg *: F + P + P + G *: sf) + 2 *: (gz *: F + G *: dz).
Proof.
rewrite -dgpr_heat_product_algebra (scalerDr G (af + sf)) (scalerDl F (ag + sg)) (scalerDr 2 (gz *: F)).
rewrite !scalerA (mulrC G 2).
set u := G *: (af + sf); set w := (ag + sg) *: F; set p := 2 *: P; set c := (2 * gz) *: F.
set d := (2 * G) *: dz.
rewrite [w + u]addrC -!addrA; congr (_ + _).
rewrite addrCA; congr (_ + _).
by rewrite addrC (addrC c p) -addrA.
Qed.

(** Source for [dgpr_jet_heat_product]: blueprint lem:heat_calculus,
    proof of (S) and (product): the Leibniz rule
    H(g f) = (H g) f + g (H f) + 2 Df(grad g) at (t,x), for a real
    function g and a vector valued function f, computed from their jets. *)
Lemma dgpr_jet_heat_product (Z : lmodType R) (NZ : Z -> R) (hNZ : is_real_norm NZ)
    (g : TX -> R) (f : TX -> Z) (ag : R) (Dg D2g : X -> X -> R) (af : Z) (Df D2f : X -> X -> Z) :
  @dgpr_heat_jet R n R^o A1 g t x ag Dg D2g -> dgpr_heat_jet NZ f t x af Df D2f ->
  dgpr_heat_operator NZ (fun q => g q *: f q) t x
    ((ag + @dgpr_laplacian_values R n R^o D2g) *: f (t, x)
      + g (t, x) *: (af + dgpr_laplacian_values D2f) + 2 *: Df x (dgpr_gradient_values (Dg x))).
Proof.
move=> hg hf; have [_ [hDf _]] := hf.
apply: (@eq_ind _ _ _ (dgpr_heat_operator_of_jet (dgpr_heat_jet_scalar_product hNZ hg hf))).
rewrite /dgpr_laplacian_values !big_split /= (dgpr_values_gradient_sum (Dg x) (hDf x)).
rewrite -scaler_suml -scaler_sumr.
exact: esym (dgpr_heat_product_algebra _ _ _ _ _ _ _).
Qed.

(** Source for [dgpr_jet_drift_product]: blueprint lem:heat_calculus,
    proof of (product): the Leibniz rule
    H_zeta(g f) = g H_zeta f + (H_zeta g) f + 2 Df(grad g) at (t,x), for
    a real function g and a vector valued function f, computed from their
    jets, with H_zeta f = d/dt f + Delta f + 2 Df(zeta) (DPGPR 2026, (3.6)). *)
Lemma dgpr_jet_drift_product (Z : lmodType R) (NZ : Z -> R) (hNZ : is_real_norm NZ) (zeta : X)
    (g : TX -> R) (f : TX -> Z) (ag : R) (Dg D2g : X -> X -> R) (af : Z) (Df D2f : X -> X -> Z) :
  @dgpr_heat_jet R n R^o A1 g t x ag Dg D2g -> dgpr_heat_jet NZ f t x af Df D2f ->
  dgpr_heat_operator_drift NZ zeta (fun q => g q *: f q) t x
    (g (t, x) *: (af + dgpr_laplacian_values D2f + 2 *: Df x zeta)
      + (ag + @dgpr_laplacian_values R n R^o D2g + 2 * Dg x zeta) *: f (t, x)
      + 2 *: Df x (dgpr_gradient_values (Dg x))).
Proof.
move=> hg hf; have [_ [hDf _]] := hf.
apply: (@eq_ind _ _ _ (dgpr_heat_operator_drift_of_jet zeta (dgpr_heat_jet_scalar_product hNZ hg hf))).
rewrite /dgpr_laplacian_values !big_split /= (dgpr_values_gradient_sum (Dg x) (hDf x)).
rewrite -scaler_suml -scaler_sumr.
exact: esym (dgpr_drift_product_algebra _ _ _ _ _ _ _ _ _).
Qed.

(** Source for [dgpr_jet_drift_square]: blueprint lem:heat_calculus,
    proof of (square): H_zeta |f|^2 = 2 CZ(f, H_zeta f) + 2 |Df|^2 at
    (t,x), where |Df|^2 = sum_i CZ(Df(eps_i), Df(eps_i)), computed from
    the jet of f. *)
Lemma dgpr_jet_drift_square (Z : lmodType R) (CZ : Z -> Z -> R) (hCZ : is_inner_product CZ)
    (zeta : X) (f : TX -> Z) (a : Z) (Df D2 : X -> X -> Z) :
  dgpr_heat_jet (inner_norm hCZ) f t x a Df D2 ->
  @dgpr_heat_operator_drift R n R^o A1 zeta (fun q => CZ (f q) (f q)) t x
    (2 * CZ (f (t, x)) (a + dgpr_laplacian_values D2 + 2 *: Df x zeta)
      + 2 * \sum_(i < n) CZ (Df x (eps i)) (Df x (eps i))).
Proof.
move=> hf; have hB := inner_bilinear hCZ.
apply: (@eq_ind _ _ _ (dgpr_heat_operator_drift_of_jet zeta (dgpr_heat_jet_inner_square hf))).
rewrite /dgpr_laplacian_values !big_split /= -!mulr_sumr.
rewrite !(bilDr hB) (bilZr hB).
rewrite (big_morph (CZ (f (t, x))) (bilDr hB (f (t, x))) (bil0r hB (f (t, x)))).
change (2 * CZ (f (t, x)) a + (2 * \sum_(i < n) CZ (Df x (eps i)) (Df x (eps i))
    + 2 * \sum_(i < n) CZ (f (t, x)) (D2 (eps i) (eps i))) + 2 * (2 * CZ (f (t, x)) (Df x zeta)) =
  2 * (CZ (f (t, x)) a + \sum_(i < n) CZ (f (t, x)) (D2 (eps i) (eps i)) + 2 * CZ (f (t, x)) (Df x zeta))
    + 2 * \sum_(i < n) CZ (Df x (eps i)) (Df x (eps i))).
ring.
Qed.

(** Source for [dgpr_jet_drift_chain]: blueprint lem:heat_calculus,
    proof of (chain): H_zeta(Phi o phi) = Phi'(phi) H_zeta phi +
    Phi''(phi) |Dphi|^2 at (t,x), where |Dphi|^2 = sum_i Dphi(eps_i)^2,
    for a positive real function phi and a real function Phi with
    derivatives Phi1 and Phi2 = Phi1' on (0,infinity). *)
Lemma dgpr_jet_drift_chain (Phi Phi1 Phi2 : R -> R) (zeta : X) (phi : TX -> R) (a : R)
    (Dphi D2 : X -> X -> R) :
  (forall r, 0 < r -> has_real_curve_derivative Phi r (Phi1 r)) ->
  (forall r, 0 < r -> has_real_curve_derivative Phi1 r (Phi2 r)) ->
  (forall y, 0 < phi (t, y)) ->
  @dgpr_heat_jet R n R^o A1 phi t x a Dphi D2 ->
  @dgpr_heat_operator_drift R n R^o A1 zeta (fun q => Phi (phi q)) t x
    (Phi1 (phi (t, x)) * (a + @dgpr_laplacian_values R n R^o D2 + 2 * Dphi x zeta)
      + Phi2 (phi (t, x)) * \sum_(i < n) Dphi x (eps i) ^+ 2).
Proof.
move=> hPhi hPhi1 hpos hphi.
apply: (@eq_ind _ _ _ (dgpr_heat_operator_drift_of_jet zeta (dgpr_heat_jet_compose hPhi hPhi1 hpos hphi))).
rewrite /dgpr_laplacian_values big_split /=.
have -> : \sum_(i < n) (Phi2 (phi (t, x)) * Dphi x (eps i) * Dphi x (eps i) : R^o) =
    Phi2 (phi (t, x)) * \sum_(i < n) Dphi x (eps i) ^+ 2.
  by rewrite mulr_sumr; apply: eq_bigr => i _; rewrite -mulrA expr2.
have -> : \sum_(i < n) (Phi1 (phi (t, x)) * D2 (eps i) (eps i) : R^o) =
    Phi1 (phi (t, x)) * \sum_(i < n) D2 (eps i) (eps i).
  by rewrite mulr_sumr.
change (Phi1 (phi (t, x)) * a + (Phi2 (phi (t, x)) * \sum_(i < n) Dphi x (eps i) ^+ 2
    + Phi1 (phi (t, x)) * \sum_(i < n) D2 (eps i) (eps i)) + 2 * (Phi1 (phi (t, x)) * Dphi x zeta) =
  Phi1 (phi (t, x)) * (a + \sum_(i < n) D2 (eps i) (eps i) + 2 * Dphi x zeta)
    + Phi2 (phi (t, x)) * \sum_(i < n) Dphi x (eps i) ^+ 2).
ring.
Qed.

End Identities.
