(** De Philippis, De Rosa and Ghiraldin (2018), (A.7) and (A.8), p. 1144;
    blueprint new:BFderiv. For T ∈ G(n, d), L ∈ Hom(R^n, R^n) and the
    moving plane T(t), the orthogonal projection onto (1 + t L)[im T],

        ||∧_d T|| = 1,
        d/dt ||∧_d((1 + t L) ∘ T)|| at t = 0 equals L • T,
        d/dt (F(T(t)) ||∧_d((1 + t L) ∘ T)||) at t = 0 equals B_F(T) • L,

    for an integrand F not depending on the point; the frozen integrand
    F(x, ·) of a point-dependent integrand is of this kind. The second
    formula is Allard 2.4(1). The third combines Lemma A.1, the chain rule
    of Federer 3.1.1(2) and 3.1.22, and the product rule. All derivatives
    are the two-sided derivatives of Federer 2.9.19, p. 163. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals ring lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities
  LinearBasis Bilinear TensorUP Hom HomInner HomInnerCoordinates AdjointUP AdjointLaws Adjoint
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates EuclideanRectangularAdjoint
  HilbertFormCompactness RealNormUP PartialFunctionUP TangentConeUP NormDifferentialUP
  NormDifferentialChain NormDifferentialScalar NormHigherCurveDerivativeUP
  NormedCurveDerivativeUP NormedCurveLocalAgreement RealCurveDerivativeUP
  RealCurvePolynomialDerivatives RelativeClassUP RelativeDifferentialUP OrthonormalFamilies
  ExteriorNorm FiniteExteriorPowers EuclideanLinearMaps EuclideanLinearJacobian.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann
  AllardProjectionFormula AllardJacobians.
From DPDRG Require Import DdgLinearAlgebra DdgGrassmann DdgMovingPlane DdgLemmaA1
  DdgGrassmannTangent DdgHomInner DdgAnisotropicIntegrandUP DdgAnisotropicIntegrand.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ddg_real_curve_local]: Federer 2.9.19, p. 163: the
    derivative at x depends only on the values near x. Supporting
    lemma. *)
Lemma ddg_real_curve_local (R : realType) (f g : R -> R) (x r v : R) :
  0 < r -> (forall t, `|t - x| < r -> f t = g t) ->
  has_real_curve_derivative f x v -> has_real_curve_derivative g x v.
Proof.
move=> hr hfg hf.
apply/(scalar_normed_curve_derivative g x v).
apply: (@normed_curve_derivative_neighbourhood_agreement R R^o (fun y => `|y|) f g x r v hr hfg).
exact/(scalar_normed_curve_derivative f x v).
Qed.

(** Source for [ddg_curve_chain]: Federer 3.1.1(2), p. 210, and the first
    special case of 3.1.1, p. 209: if g is differentiable at a with
    differential D, P(0) = a and P'(0) = v, then (g ∘ P)'(0) = D(v), and
    P(t) lies in the domain of g for t near 0. Supporting lemma. *)
Lemma ddg_curve_chain (R : realType) (X : lmodType R) (NX : X -> R) (hNX : is_real_norm NX)
    (U : X -> Prop) (g : X -> R^o) (P : R -> X) (a v : X) (D : Hom X R^o) :
  P 0 = a -> has_normed_curve_derivative NX P 0 v ->
  has_norm_differential NX (fun t : R^o => `|t|) U g a D ->
  has_real_curve_derivative (fun t => g (P t)) 0 (D v) /\
  exists2 r : R, 0 < r & forall t, `|t| < r -> U (P t).
Proof.
move=> hP0 hP hg.
have hP' : has_norm_differential (fun t : R^o => `|t|) NX (fun _ => True) P 0
    (scalar_coefficient_linear_map v).
  apply: (@norm_differential_real_source R X NX hNX (fun _ => True) P 0
    (scalar_coefficient_linear_map v)).2; split.
    by exists 1; split=> //; exact: ltr01.
  have h1 : scalar_coefficient_linear_map v 1 = v.
    by change ((1 : R) *: v = v); rewrite scale1r.
  by rewrite h1.
rewrite -hP0 in hg.
have hc := norm_differential_chain (@scalar_absolute_value_norm R) hNX
  (@scalar_absolute_value_norm R) hP' hg.
have e : hom_comp D (scalar_coefficient_linear_map v) = scalar_coefficient_linear_map (D v).
  apply: hom_ext=> t; rewrite hom_compE.
  by change (D (t *: v) = t *: D v); exact: linearZ.
rewrite e in hc.
split; first exact: real_curve_derivative_from_differential hc.
have [r [hr hU]] := norm_differential_interior hc.
exists r=> // t ht; have := hU t ht; rewrite add0r; by case.
Qed.

Section WeightedJacobian.
Variable R : realType.
Variables n d : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation NH := (hom_norm hBn hBn hbn).
Local Notation hNH := (inner_norm_real_norm (hom_inner_productP hBn hBn hbn)).
Local Notation N1 := (fun t : R^o => `|t|).
Local Notation hN1 := (@scalar_absolute_value_norm R).
Local Notation HI := (hom_inner hBn hBn hbn).
Local Notation idn := (hom_of_linear (linear_id Rn)).
Local Notation G := (orthogonal_projectors R n d).

(** Source for [ddg_jacobian_projection]: blueprint new:BFderiv:
    ||∧_d T|| = 1 for T ∈ G(n, d), the Jacobian of Federer 3.2.1, p. 241.
    By Allard 2.4, ||∧_d T|| = |u_1 ∧ ⋯ ∧ u_d| for an orthonormal basis
    u_1, …, u_d of im T, and this is 1 by Federer 1.7.5, p. 32. Direct
    formalisation. *)
Theorem ddg_jacobian_projection (T : Hom Rn Rn) : G T -> euclidean_linear_jacobian d T = 1.
Proof.
move=> hT.
have [u [hu hTu]] := projection_grassmann_frame (projection_grassmann_of hT).
have hTu' : T = frame_projector hBn u := hTu.
have -> : T = hom_comp idn (frame_projector hBn u).
  by rewrite -hTu'; apply: hom_ext=> x; rewrite hom_compE ddg_hom_idE.
rewrite (@allard_2_4 R n n d idn u hu).
rewrite -[RHS](orthonormal_product_unit_norm (euclidean_two_nonzero R) hBn hu).
by congr (exterior_norm _ _ (e_lambda _ _)); apply/funext=> i; exact: ddg_hom_idE.
Qed.

(** Source for [ddg_jacobian_derivative]: DDG (A.7), p. 1144, Allard
    2.4(1), p. 422; blueprint new:BFderiv, first formula:
    d/dt ||∧_d((1 + t L) ∘ T)|| at t = 0 equals L • T. Direct
    formalisation. *)
Theorem ddg_jacobian_derivative (L T : Hom Rn Rn) :
  G T ->
  has_real_curve_derivative
    (fun t => euclidean_linear_jacobian d (hom_comp (idn + t *: L) T)) 0 (HI L T).
Proof. by move=> hT; exact: (allard_2_4_1 L (projection_grassmann_of hT)). Qed.

(** Source for [ddg_weighted_jacobian_derivative]: DDG (A.8), p. 1144;
    blueprint new:BFderiv, second formula: if B satisfies the
    characterising equation of B_F(T) and T(t) is the orthogonal projection
    onto (1 + t L)[im T] for |t| < δ, then
    d/dt (F(T(t)) ||∧_d((1 + t L) ∘ T)||) at t = 0 equals B • L. Direct
    formalisation. *)
Theorem ddg_weighted_jacobian_derivative (F : Hom Rn Rn -> R) (T B L : Hom Rn Rn)
    (P : R -> Hom Rn Rn) :
  G T -> is_ddg_B d F T B ->
  (exists2 delta : R, 0 < delta &
    forall t, `|t| < delta -> is_ddg_plane_projection d (idn + t *: L) T (P t)) ->
  has_real_curve_derivative
    (fun t => F (P t) * euclidean_linear_jacobian d (hom_comp (idn + t *: L) T)) 0 (HI B L).
Proof.
move=> hT [Lp [[_ [U [g [D [hD [hag hres]]]]]] hB]] hPd.
have hP := ddg_lemma_A_1 hT hPd.
have [delta hdelta hPt] := hPd.
have hP0 : P 0 = T.
  by apply: (ddg_plane_zero (L := L) hT); apply: hPt; rewrite normr0.
have [hgP [r hr hU]] := ddg_curve_chain hNH hP0 hP hD.
have hDv : D (ddg_tangent_direction T L) = HI B L - F T * HI T L.
  have h1 : partial_function_graph Lp (ddg_tangent_direction T L) (D (ddg_tangent_direction T L)).
    by apply/hres; split=> //; exact: ddg_tangent_direction_tangent.
  exact: partial_function_single_valued h1 (hB L).
rewrite hDv in hgP.
have hFP : has_real_curve_derivative (fun t => F (P t)) 0 (HI B L - F T * HI T L).
  apply: (ddg_real_curve_local (r := Num.min r delta)) hgP.
    by rewrite lt_min hr hdelta.
  move=> t; rewrite subr0 lt_min=> /andP [htr htd].
  have [hG _] := hPt t htd.
  by have [_ ->] := hag (P t) hG (hU t htr).
have hprod := real_curve_derivative_product hFP (ddg_jacobian_derivative L hT).
cbv beta in hprod.
have hJ0 : euclidean_linear_jacobian d (hom_comp (idn + 0 *: L) T) = 1.
  rewrite scale0r addr0.
  have -> : hom_comp idn T = T by apply: hom_ext=> x; rewrite hom_compE ddg_hom_idE.
  exact: ddg_jacobian_projection hT.
rewrite hJ0 hP0 (ddg_hom_inner_sym L T) in hprod.
have e : HI B L = (HI B L - F T * HI T L) * 1 + F T * HI T L by ring.
by rewrite [X in has_real_curve_derivative _ _ X]e.
Qed.

(** Source for [ddg_moving_plane_family]: blueprint new:projformula: the
    curve T(t) = [[ddg_moving_plane L T t]] is the orthogonal projection
    onto (1 + t L)[im T] for |t| < (|L| + 1)^{-1}. Supporting lemma. *)
Lemma ddg_moving_plane_family (L T : Hom Rn Rn) :
  G T ->
  exists2 delta : R, 0 < delta &
    forall t, `|t| < delta -> is_ddg_plane_projection d (idn + t *: L) T (ddg_moving_plane L T t).
Proof.
move=> hT; exists (1 / (NH L + 1)).
  by rewrite divr_gt0 // ltr_pwDr // ddg_hom_norm_nonnegative.
move=> t ht; apply: ddg_moving_planeP=> //.
have hc0 := ddg_hom_norm_nonnegative L.
have h1 : NH L * `|t| <= (NH L + 1) * `|t| by rewrite ler_wpM2r //; lra.
have h2 : (NH L + 1) * `|t| < (NH L + 1) * (1 / (NH L + 1)).
  by rewrite ltr_pM2l //; lra.
have h3 : (NH L + 1) * (1 / (NH L + 1)) = 1 by field; rewrite gt_eqF //; lra.
by rewrite -h3; exact: le_lt_trans h1 h2.
Qed.

(** Source for [ddg_B_derivative]: DDG (A.8), p. 1144; blueprint
    new:BFderiv: for F of class 1 relative to G(n, d), T ∈ G(n, d) and
    L ∈ Hom(R^n, R^n),
    B_F(T) • L = d/dt (F(T(t)) ||∧_d((1 + t L) ∘ T)||) at t = 0. Direct
    formalisation. *)
Theorem ddg_B_derivative (F : Hom Rn Rn -> R) (T L : Hom Rn Rn) :
  G T -> @norm_class_relative R _ R^o NH N1 hNH hN1 G G F 1 ->
  has_real_curve_derivative
    (fun t => F (ddg_moving_plane L T t) * euclidean_linear_jacobian d (hom_comp (idn + t *: L) T))
    0 (HI (ddg_B d F T) L).
Proof.
move=> hT hF.
exact: ddg_weighted_jacobian_derivative hT (ddg_B_class_one hT hF) (ddg_moving_plane_family L hT).
Qed.

End WeightedJacobian.
