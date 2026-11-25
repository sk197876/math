(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3, (3.6)
    and the identities in the proof of Lemma 3.1; blueprint
    dgpr_blueprint.tex, lem:identities(heat) for S and lem:heat_calculus.

    The value H_zeta f(t,x) = h is the relation
    [dgpr_heat_Hzeta hS NZ f t x h]; it includes the existence of the
    second order jet of f at (t,x), that is, the hypothesis that f is of
    class 2 near (t,x) in the sense of DgprHeatJets.v. The differential
    D f_t(x) enters through its values l, given by
    [dgpr_differential_values NZ (fun z => f (t, z)) x l]. The squared norm
    |D f_t(x)|^2 of Federer 1.7.9 is the sum
    sum_i CZ(D f_t(x)(eps_i), D f_t(x)(eps_i)) over the standard basis eps
    (blueprint mr:notation), and |grad phi_t(x)|^2 is the square of the
    euclidean norm of the gradient. Jets depend only on the values on
    Omega_T ([dgpr_heat_jet_local]); this replaces the identities
    W = S B and rho = S q, which hold on Omega_T. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CoordinateProjection FiniteCoordinates LinearBasis HomInner
  ScalarInnerProduct CompleteMetricUP PartialFunctionUP PartialFunctionBasic MeasureUP RadonMeasureUP
  ScalarNormMetricCompleteness LocalUniquenessExample SmoothFunctionSpaceUP SmoothTestSpaces
  NormedCurveDerivativeUP RealCurveDerivativeUP SignedSquareRootDerivative.
From DPGPR Require Import DgprDifferentialCalculus DgprHeatKernel DgprHeatKernelFamily DgprHeatExtension
  DgprHeatSemiconvex DgprHeatJets DgprHeatJetCalculus DgprBackwardHeat DgprStanding DgprHeatObjects
  DgprIdentities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Locality.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation TX := ((R^o * R_n R n)%type).

(** Source for [dgpr_curve_local]: Federer 2.9.22, p. 167: the
    derivative of a curve at t depends only on its values near t. *)
Lemma dgpr_curve_local (Z : lmodType R) (NZ : Z -> R) (f g : R -> Z) (t r : R) (a : Z) :
  0 < r -> (forall s, `|s - t| < r -> f s = g s) ->
  has_normed_curve_derivative NZ f t a -> has_normed_curve_derivative NZ g t a.
Proof.
move=> hr hfg hf e he; have [d [hd hdf]] := hf e he.
exists (Num.min d r); split; first by rewrite lt_min hd hr.
move=> h /andP [h0 hh]; move: hh; rewrite lt_min => /andP [hhd hhr].
rewrite -(hfg (t + h)); last by rewrite addrAC subrr add0r.
rewrite -(hfg t); last by rewrite subrr normr0.
by apply: hdf; rewrite h0 hhd.
Qed.

(** Source for [dgpr_heat_jet_local]: the jet of DgprHeatJets.v at
    (t,x) with t < T depends only on the values on Omega_T (Federer
    2.9.22 and 3.1.1). *)
Lemma dgpr_heat_jet_local (T : R) (Z : lmodType R) (NZ : Z -> R) (f g : TX -> Z) (t : R) (x : X) a
    (Df D2 : X -> X -> Z) :
  t < T -> (forall q : TX, q.1 < T -> f q = g q) ->
  dgpr_heat_jet NZ f t x a Df D2 -> dgpr_heat_jet NZ g t x a Df D2.
Proof.
move=> ht hfg [hc [hD hD2]]; split; [|split] => //.
- apply: (dgpr_curve_local (r := T - t)) hc; first by rewrite subr_gt0.
  move=> s hs; apply: hfg => /=.
  have := ler_norm (s - t); lra.
- move=> y; apply: (dgpr_values_ext _ _ (hD y)) => // z; exact: hfg.
Qed.

(** Source for [dgpr_heat_operator_local]: H f(t,x) with t < T depends
    only on the values of f on Omega_T; def:heat_objects. *)
Lemma dgpr_heat_operator_local (T : R) (Z : lmodType R) (NZ : Z -> R) (f g : TX -> Z) (t : R) (x : X)
    (h : Z) :
  t < T -> (forall q : TX, q.1 < T -> f q = g q) ->
  dgpr_heat_operator NZ f t x h -> dgpr_heat_operator NZ g t x h.
Proof.
move=> ht hfg [a [Df [D2 [hj ->]]]]; exists a, Df, D2; split => //.
exact: (dgpr_heat_jet_local ht hfg hj).
Qed.

(** Source for [dgpr_heat_jet_values_ext]: the jet relation depends only
    on the values of its components; supporting def:heat_objects. *)
Lemma dgpr_heat_jet_values_ext (Z : lmodType R) (NZ : Z -> R) (f : TX -> Z) (t : R) (x : X) (a a' : Z)
    (Df Df' D2 D2' : X -> X -> Z) :
  a = a' -> (forall y v, Df y v = Df' y v) -> (forall v w, D2 v w = D2' v w) ->
  dgpr_heat_jet NZ f t x a Df D2 -> dgpr_heat_jet NZ f t x a' Df' D2'.
Proof.
move=> <- eD e2.
have -> : Df' = Df by apply: funext => y; apply: funext => v; rewrite eD.
by have -> : D2' = D2 by apply: funext => v; apply: funext => w; rewrite e2.
Qed.

(** Source for [dgpr_values_scaleE]: Federer 3.1.1, p. 209: the values
    of a differential are linear in the direction. *)
Lemma dgpr_values_scaleE (Z : lmodType R) (NZ : Z -> R) (f : X -> Z) (a : X) (l : X -> Z) (c : R) (v : X) :
  dgpr_differential_values NZ f a l -> l (c *: v) = c *: l v.
Proof. by move=> [L [_ hL]]; rewrite -!hL linearZ. Qed.

End Locality.

Section HeatCalculus.
Variable R : realType.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Local Notation eps := (@coordinate_basis R n).
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
Local Notation BD := (hom_inner_productP hCY (scalar_inner_productP R) heY).
Local Notation ND := (hom_norm hCY (scalar_inner_productP R) heY).
Local Notation hND := (inner_norm_real_norm BD).
Local Notation hZ1 := (@scalar_norm_metric_complete R).
Local Notation hsep1 := (scalar_norm_separable R).
Local Notation hHc := (@dgpr_hom_space_complete R n Y CY hCY d eY heY).
Local Notation hHs := (@dgpr_hom_space_separable R n Y CY hCY d eY heY).
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
Local Notation hmu := (dgpr_standing_mu_measure hS).
Local Notation hups := (dgpr_standing_ups_measure hS).
Local Notation hmu0 := (dgpr_standing_mu0_measure hS).
Local Notation hOmu := (dgpr_standing_mu_borel hS).
Local Notation hOups := (radon_open_measurable (dgpr_standing_ups_radon hS)).
Local Notation hOmu0 := (dgpr_standing_mu0_borel hS).
Local Notation hMmu := (dgpr_standing_mu_mass hS).
Local Notation hMups := (dgpr_standing_ups_mass hS).
Local Notation hMmu0 := (dgpr_standing_mu0_mass hS).
Local Notation one := (fun _ : X => (1 : R^o)).
Local Notation U := (dgpr_heat_U hS).
Local Notation W := (dgpr_heat_W hS).
Local Notation Rr := (dgpr_heat_R hS).
Local Notation Psi := (dgpr_heat_Psi hS).
Local Notation S := (dgpr_heat_S hS).
Local Notation rho := (dgpr_heat_rho hS).
Local Notation B := (dgpr_heat_B hS).
Local Notation Q := (dgpr_heat_q hS).
Local Notation kappa := (dgpr_heat_kappa hS).
Local Notation zeta := (dgpr_heat_zeta hS).
Local Notation D2U t x := (dgpr_backward_second hmu hZ1 one T t x).
Local Notation D2R t x := (dgpr_backward_second hups hZ1 one T t x).

(** Source for [dgpr_sqrt_time_jet]: the jet at (t,x), t < T, of
    [(r,z) |-> (T - r)^(1/2)]: its time derivative is
    -(2 (T - t)^(1/2))^(-1) (Federer 3.1.1(3) and the derivative of the
    square root), and its space differentials vanish; supporting
    blueprint proof of lem:identities(heat). *)
Lemma dgpr_sqrt_time_jet (t : R) (x : X) : t < T ->
  @dgpr_heat_jet R n R^o A1 (fun q : TX => Num.sqrt (T - q.1)) t x (- (2 * Num.sqrt (T - t))^-1)
    (fun _ _ => 0) (fun _ _ => 0).
Proof.
move=> ht; have hs : 0 < T - t by rewrite subr_gt0.
split; [|split].
- apply/scalar_normed_curve_derivative.
  have h1 := dgpr_real_curve_affine T (-1) t.
  have hs' : 0 < T + t * -1 by rewrite mulrN1.
  have h : has_real_curve_derivative (fun r => Num.sqrt (T + r * -1)) t
      ((2 * Num.sqrt (T + t * -1))^-1 * -1).
    exact: (dgpr_real_curve_chain h1 (positive_square_root_real_derivative hs')).
  have e : (fun r => Num.sqrt (T + r * -1)) = (fun r => Num.sqrt (T - r)).
    by apply: funext => r; rewrite mulrN1.
  by move: h; rewrite e !mulrN1.
- move=> y; exact: (dgpr_values_constant hA (Num.sqrt (T - t)) y).
- move=> w; exact: (dgpr_values_constant hA (0 : R^o) x).
Qed.

(** Source for [dgpr_heat_S_jet]: blueprint proof of
    lem:identities(heat): the jet of S = U + (T - t)^(1/2) R at (t,x),
    t < T, from the jets of U and R (DgprBackwardHeat.v) and the Leibniz
    rule; the space differential of S_t is [dgpr_heat_S_first]. *)
Theorem dgpr_heat_S_jet (t : R) (x : X) : t < T ->
  @dgpr_heat_jet R n R^o A1 S t x
    (- dgpr_laplacian_values (D2U t x) +
      (- (2 * Num.sqrt (T - t))^-1 * Rr (t, x) - Num.sqrt (T - t) * dgpr_laplacian_values (D2R t x)))
    (dgpr_heat_S_first hS t) (fun v w => D2U t x v w + Num.sqrt (T - t) * D2R t x v w).
Proof.
move=> ht.
have jU := dgpr_backward_heat_jet hmu hZ1 hOmu hMmu hsep1 (dgpr_one_measurable hmu) (@dgpr_one_bound1 R n) x ht.
have jR := dgpr_backward_heat_jet hups hZ1 hOups hMups hsep1 (dgpr_one_measurable hups) (@dgpr_one_bound1 R n) x ht.
have jS := dgpr_heat_jet_add hA jU (dgpr_heat_jet_scalar_product hA (dgpr_sqrt_time_jet x ht) jR).
apply: (dgpr_heat_jet_values_ext _ _ _ jS).
- by rewrite /= scalerN.
- by move=> y v; rewrite /dgpr_heat_S_first /= scale0r add0r.
- by move=> v w; rewrite /= !scale0r !add0r.
Qed.

(** Source for [dgpr_identities_heat_S]: blueprint lem:identities(heat),
    last equation, and DPGPR 2026, (3.3)-(3.4): H S = - kappa S on
    Omega_T, since H((T - t)^(1/2) R) = -2^(-1) (T - t)^(-1/2) R +
    (T - t)^(1/2) H R = - kappa S and H U = H R = 0. *)
Theorem dgpr_identities_heat_S (t : R) (x : X) : t < T ->
  @dgpr_heat_operator R n R^o A1 S t x (- (kappa (t, x) * S (t, x))).
Proof.
move=> ht; have hs : 0 < T - t by rewrite subr_gt0.
have hq : 0 < Num.sqrt (T - t) by rewrite sqrtr_gt0.
have hS0 := dgpr_identities_S_pos hS x ht.
apply: (@eq_ind _ _ _ (dgpr_heat_operator_of_jet (dgpr_heat_S_jet x ht))).
rewrite /dgpr_laplacian_values big_split /= -mulr_sumr /dgpr_heat_kappa /=.
set a := \sum_(i < n) _; set b := \sum_(i < n) _.
have e : Rr (t, x) / (2 * Num.sqrt (T - t) * S (t, x)) * S (t, x) = Rr (t, x) * (2 * Num.sqrt (T - t))^-1.
  by rewrite invfM -!mulrA mulVf ?gt_eqF ?mulr1.
rewrite e; set c := (2 * Num.sqrt (T - t))^-1.
ring.
Qed.

(** Source for [dgpr_identities_heat]: blueprint lem:identities(heat) and
    DPGPR 2026, (3.3): H U = H W = H R = H Psi = H rho = 0 and
    H S = - kappa S on Omega_T. *)
Theorem dgpr_identities_heat (t : R) (x : X) : t < T ->
  [/\ @dgpr_heat_operator R n R^o A1 U t x 0, dgpr_heat_operator NH W t x 0,
      @dgpr_heat_operator R n R^o A1 Rr t x 0,
      dgpr_heat_operator ND Psi t x 0 /\ @dgpr_heat_operator R n R^o A1 rho t x 0 &
      @dgpr_heat_operator R n R^o A1 S t x (- (kappa (t, x) * S (t, x)))].
Proof.
move=> ht; have [h1 h2 h3 h4 h5] := dgpr_identities_heat_extensions hS x ht.
by split => //; exact: dgpr_identities_heat_S.
Qed.

(** Source for [dgpr_heat_S_gradient]: grad S_t(x) = S(t,x) zeta(t,x) on
    Omega_T, by the definition of zeta; blueprint proof of
    lem:heat_calculus(S). *)
Lemma dgpr_heat_S_gradient (t : R) (x : X) : t < T ->
  dgpr_gradient_values (dgpr_heat_S_first hS t x) = S (t, x) *: zeta (t, x).
Proof.
move=> ht; have hS0 := dgpr_identities_S_pos hS x ht.
by rewrite /dgpr_heat_zeta /= scalerA mulfV ?gt_eqF ?scale1r.
Qed.

(** Source for [dgpr_heat_calculus_S]: blueprint lem:heat_calculus(S) and
    DPGPR 2026, proof of Lemma 3.1: H(S f) = S H_zeta f - kappa S f on
    Omega_T, from H(S f) = (H S) f + S H f + 2 D f(grad S),
    H S = - kappa S and grad S = S zeta. *)
Theorem dgpr_heat_calculus_S (Z : lmodType R) (NZ : Z -> R) (hNZ : is_real_norm NZ) (f : TX -> Z)
    (t : R) (x : X) (h : Z) :
  t < T -> dgpr_heat_Hzeta hS NZ f t x h ->
  dgpr_heat_operator NZ (fun q => S q *: f q) t x (S (t, x) *: h - (kappa (t, x) * S (t, x)) *: f (t, x)).
Proof.
move=> ht [a [Df [D2 [hj ->]]]].
have hp := dgpr_jet_heat_product hNZ (dgpr_heat_S_jet x ht) hj.
apply: (@eq_ind _ _ _ hp).
have hHS := dgpr_identities_heat_S x ht.
have hHS' := dgpr_heat_operator_of_jet (dgpr_heat_S_jet x ht).
rewrite (dgpr_heat_operator_unique hA hHS' hHS) (dgpr_heat_S_gradient x ht).
have [_ [hDf _]] := hj.
rewrite (dgpr_values_scaleE _ _ (hDf x)) scalerDr scalerA (mulrC 2) -scalerA scaleNr.
rewrite !scalerDr !scalerA.
by rewrite -addrA addrC.
Qed.

(** Source for [dgpr_heat_calculus_product]: blueprint
    lem:heat_calculus(product): H_zeta(g f) = g H_zeta f + (H_zeta g) f +
    2 D f_t(x)(grad g_t(x)), the Leibniz rule (Federer 3.1.11). *)
Theorem dgpr_heat_calculus_product (Z : lmodType R) (NZ : Z -> R) (hNZ : is_real_norm NZ)
    (g : TX -> R) (f : TX -> Z) (t : R) (x : X) (hf : Z) (hg : R) (lf : X -> Z) (lg : X -> R) :
  dgpr_heat_Hzeta hS NZ f t x hf -> dgpr_heat_Hzeta hS A1 g t x hg ->
  dgpr_differential_values NZ (fun z => f (t, z)) x lf ->
  dgpr_differential_values A1 (fun z => g (t, z)) x lg ->
  dgpr_heat_Hzeta hS NZ (fun q => g q *: f q) t x
    (g (t, x) *: hf + hg *: f (t, x) + 2 *: lf (dgpr_gradient_values lg)).
Proof.
move=> [af [Df [D2f [jf ->]]]] [ag [Dg [D2g [jg ->]]]] hlf hlg.
have hp := dgpr_jet_drift_product hNZ (zeta (t, x)) jg jf.
have [_ [hDf _]] := jf; have [_ [hDg _]] := jg.
have e1 : Df x (dgpr_gradient_values (Dg x)) = lf (dgpr_gradient_values lg).
  have -> : dgpr_gradient_values (Dg x) = dgpr_gradient_values lg.
    by apply: eq_bigr => i _; rewrite (dgpr_differential_values_unique hA (hDg x) hlg).
  exact: (dgpr_differential_values_unique hNZ (hDf x) hlf).
by rewrite -e1.
Qed.

(** Source for [dgpr_heat_calculus_square]: blueprint
    lem:heat_calculus(square): H_zeta |f|^2 = 2 f . H_zeta f +
    2 |D f_t(x)|^2, with |f|^2 = CZ(f,f) and
    |D f_t(x)|^2 = sum_i CZ(D f_t(x)(eps_i), D f_t(x)(eps_i)). *)
Theorem dgpr_heat_calculus_square (Z : lmodType R) (CZ : Z -> Z -> R) (hCZ : is_inner_product CZ)
    (f : TX -> Z) (t : R) (x : X) (hf : Z) (lf : X -> Z) :
  dgpr_heat_Hzeta hS (inner_norm hCZ) f t x hf ->
  dgpr_differential_values (inner_norm hCZ) (fun z => f (t, z)) x lf ->
  dgpr_heat_Hzeta hS A1 (fun q => CZ (f q) (f q)) t x
    (2 * CZ (f (t, x)) hf + 2 * \sum_(i < n) CZ (lf (eps i)) (lf (eps i))).
Proof.
move=> [a [Df [D2 [jf ->]]]] hlf.
have hp := dgpr_jet_drift_square (zeta (t, x)) jf.
have [_ [hDf _]] := jf.
have e i : Df x (eps i) = lf (eps i).
  exact: (dgpr_differential_values_unique (inner_norm_real_norm hCZ) (hDf x) hlf).
have -> : \sum_(i < n) CZ (lf (eps i)) (lf (eps i)) = \sum_(i < n) CZ (Df x (eps i)) (Df x (eps i)).
  by apply: eq_bigr => i _; rewrite e.
exact: hp.
Qed.

(** Source for [dgpr_gradient_norm_sqr]: |grad f(x)|^2 =
    sum_i D f(x)(eps_i)^2 (Federer 1.7.1, 3.1.1); supporting blueprint
    lem:heat_calculus(chain). *)
Lemma dgpr_gradient_norm_sqr (f : X -> R) (a : X) (l : X -> R) :
  @dgpr_differential_values R n R^o A1 f a l ->
  N (dgpr_gradient_values l) ^+ 2 = \sum_(i < n) l (eps i) ^+ 2.
Proof.
move=> hl; rewrite inner_norm_sqr.
rewrite -(dgpr_gradient_valuesE _ hl) -(dgpr_values_linear _ hl).
apply: eq_bigr => i _.
rewrite -[dgpr_gradient_values l i](euclidean_inner_basis (dgpr_gradient_values l) i).
rewrite -(dgpr_gradient_valuesE _ hl) expr2.
by change (l (eps i) * l (eps i) = l (eps i) * l (eps i)).
Qed.

(** Source for [dgpr_heat_calculus_chain]: blueprint
    lem:heat_calculus(chain): H_zeta(Phi o phi) = (Phi' o phi) H_zeta phi
    + (Phi'' o phi) |grad phi_t(x)|^2, for phi > 0 and Phi of class 2 on
    (0,infinity) with derivatives Phi1 and Phi2 (Federer 3.1.11). *)
Theorem dgpr_heat_calculus_chain (Phi Phi1 Phi2 : R -> R) (phi : TX -> R) (t : R) (x : X) (hp : R)
    (l : X -> R) :
  (forall r, 0 < r -> has_real_curve_derivative Phi r (Phi1 r)) ->
  (forall r, 0 < r -> has_real_curve_derivative Phi1 r (Phi2 r)) ->
  (forall y, 0 < phi (t, y)) ->
  dgpr_heat_Hzeta hS A1 phi t x hp -> @dgpr_differential_values R n R^o A1 (fun z => phi (t, z)) x l ->
  dgpr_heat_Hzeta hS A1 (fun q => Phi (phi q)) t x
    (Phi1 (phi (t, x)) * hp + Phi2 (phi (t, x)) * N (dgpr_gradient_values l) ^+ 2).
Proof.
move=> hPhi hPhi1 hpos [a [Dp [D2 [jp ->]]]] hl.
have hc := dgpr_jet_drift_chain (zeta (t, x)) hPhi hPhi1 hpos jp.
have [_ [hDp _]] := jp.
rewrite (dgpr_gradient_norm_sqr hl).
have -> : \sum_(i < n) l (eps i) ^+ 2 = \sum_(i < n) Dp x (eps i) ^+ 2.
  by apply: eq_bigr => i _; rewrite (dgpr_differential_values_unique hA (hDp x) hl).
exact: hc.
Qed.

(** Source for [dgpr_heat_calculus_ratio]: blueprint proof of
    lem:heat_calculus(Bq): if F has a jet at (t,x), t < T, and H F = 0,
    then H_zeta(S^(-1) F) = kappa S^(-1) F, since S S^(-1) F = F on
    Omega_T and (S) gives H(S (S^(-1) F)) = S H_zeta(S^(-1) F) -
    kappa S (S^(-1) F). *)
Lemma dgpr_heat_calculus_ratio (Z : lmodType R) (NZ : Z -> R) (hNZ : is_real_norm NZ) (F : TX -> Z)
    (t : R) (x : X) (a : Z) (DF D2F : X -> X -> Z) :
  t < T -> dgpr_heat_jet NZ F t x a DF D2F -> dgpr_heat_operator NZ F t x 0 ->
  dgpr_heat_Hzeta hS NZ (fun q => (S q)^-1 *: F q) t x (kappa (t, x) *: ((S (t, x))^-1 *: F (t, x))).
Proof.
move=> ht jF hF.
have hpos y : 0 < S (t, y) := dgpr_identities_S_pos hS y ht.
have [hinv1 hinv2] := @dgpr_real_curve_inverse R.
have jI := dgpr_heat_jet_compose hinv1 hinv2 hpos (dgpr_heat_S_jet x ht).
have jB := dgpr_heat_jet_scalar_product hNZ jI jF.
have [vB hd] : exists vB, dgpr_heat_Hzeta hS NZ (fun q => (S q)^-1 *: F q) t x vB.
  by eexists; exact: (dgpr_heat_operator_drift_of_jet _ jB).
have hSB := dgpr_heat_calculus_S hNZ ht hd.
have hW : dgpr_heat_operator NZ F t x
    (S (t, x) *: vB - (kappa (t, x) * S (t, x)) *: ((S (t, x))^-1 *: F (t, x))).
  apply: (dgpr_heat_operator_local ht _ hSB) => -[r z] /= hr.
  have hS0 := dgpr_identities_S_pos hS z hr.
  by rewrite scalerA mulfV ?gt_eqF ?scale1r.
have e := subr0_eq (dgpr_heat_operator_unique hNZ hW hF).
have hS0 := hpos x.
suff -> : kappa (t, x) *: ((S (t, x))^-1 *: F (t, x)) = vB by exact: hd.
transitivity ((S (t, x))^-1 *: (S (t, x) *: vB)); last by rewrite scalerA mulVf ?gt_eqF ?scale1r.
by rewrite e [RHS]scalerA mulrCA mulVf ?gt_eqF ?mulr1.
Qed.

(** Source for [dgpr_heat_calculus_Bq]: blueprint lem:heat_calculus(Bq)
    and DPGPR 2026, proof of Lemma 3.1: H_zeta B = kappa B and
    H_zeta q = kappa q on Omega_T, since W = S B, rho = S q and
    H W = 0 = H rho. *)
Theorem dgpr_heat_calculus_Bq (t : R) (x : X) : t < T ->
  dgpr_heat_Hzeta hS NH B t x (kappa (t, x) *: B (t, x)) /\
  dgpr_heat_Hzeta hS A1 Q t x (kappa (t, x) * Q (t, x)).
Proof.
move=> ht; have [_ hW _ [_ hrho] _] := dgpr_identities_heat x ht.
have jW := dgpr_backward_heat_jet hmu hHc hOmu hMmu hHs (dgpr_standing_X_measurable hS)
  (fun y => dgpr_standing_K_norm hS (dgpr_standing_X_values hS y)) x ht.
have jrho := dgpr_backward_heat_jet hmu0 hZ1 hOmu0 hMmu0 hsep1 (dgpr_one_measurable hmu0)
  (@dgpr_one_bound1 R n) x ht.
split; first exact: (dgpr_heat_calculus_ratio hNH ht jW hW).
have hq := dgpr_heat_calculus_ratio hA ht jrho hrho.
have eQ : Q = (fun q => (S q)^-1 *: (rho q : R^o)).
  by apply: funext => q; rewrite /dgpr_heat_q; change (rho q * (S q)^-1 = (S q)^-1 * rho q); rewrite mulrC.
have eV : kappa (t, x) * Q (t, x) = kappa (t, x) *: ((S (t, x))^-1 *: (rho (t, x) : R^o)).
  by rewrite eQ.
rewrite eV eQ; exact: hq.
Qed.

End HeatCalculus.
