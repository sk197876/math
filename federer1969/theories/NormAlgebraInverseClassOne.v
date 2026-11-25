(** Federer (1969), 3.1.11, p. 220:
    inversion is of class one on its exact open domain.
    This is the first step toward the higher permutation formula,
    not a replacement for the full class-infinity assertion. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra.
From Federer Require Import Hom AlgebraUP RealNormUP NormMetric CompleteMetricUP
  PartialFunctionUP AlgebraInverseUP AlgebraInverse NormDifferentialUP
  NormClassOneUP NormClassOneLaws NormAlgebraInverseDifferential
  NormAlgebraInverseContinuityBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_algebra_inverse_class_one_field]:
    the degree-one regularity of inversion stated within
    Federer 3.1.11, p. 220. The displayed derivative
    and its uniform continuity are both proved on the
    exact domain of the sealed inverse graph. *)
Theorem norm_algebra_inverse_class_one_field (R : realType) (A : algebra R)
    (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (hcomplete : is_complete_metric_space (real_norm_metric_space hN))
    (F : A->A)
    (hF : forall x, partial_function_domain (algebra_inverse A) x ->
      is_two_sided_algebra_inverse x (F x)) :
  is_norm_class_one_field N N (partial_function_domain (algebra_inverse A)) F
    (fun x=>algebra_inverse_linear_term (F x)).
Proof.
have hD (x : A) (hx : partial_function_domain (algebra_inverse A) x) :=
  @norm_algebra_inverse_differential R A N hN hM hcomplete F hF x hx.
constructor.
- exact (@norm_everywhere_differentiable_class_zero R A A N N hN
  (partial_function_domain (algebra_inverse A)) F
  (fun x=>algebra_inverse_linear_term (F x)) hD).
- exact hD.
- move=> x hx e he.
  pose C := N (F x)+1.
  pose P := 6*C^+3+1.
  have hNv := real_seminorm_nonnegative hN.1 (F x).
  have hC : 0<C by rewrite /C; lra.
  have hCv : N (F x)<=C by rewrite /C; lra.
  have hC3 : 0<C^+3 by exact: exprn_gt0.
  have hP : 0<P by rewrite /P; nra.
  have h2C : 0< 2*C by nra.
  exists (Num.min ((2*C)^-1) (e/P)); split.
  + by rewrite lt_min invr_gt0 h2C divr_gt0.
  + move=> h hxh; rewrite lt_min=> /andP [hh hs] u.
    have hH0 := real_seminorm_nonnegative hN.1 h.
    have hU0 := real_seminorm_nonnegative hN.1 u.
    have hsmall : 2*C*N h<= 1.
      apply: ltW; move: hh.
      by rewrite -div1r ltr_pdivlMr // mulrC.
    have hscale : P*N h<e.
      by move: hs; rewrite ltr_pdivlMr // mulrC.
    have hcoeff : 6*C^+3*N h<=e by rewrite /P in hscale; nra.
    apply: le_trans (norm_algebra_inverse_linear_difference_bound
      hN hM (hF x hx) (hF (x+h) hxh) hC hCv hsmall u) _.
    exact (ler_wpM2r hU0 hcoeff).
Qed.

(** Source for [norm_algebra_inverse_class_one]:
    class-one regularity of inversion as a consequence
    of its explicit field, supporting the full higher
    regularity claim in Federer 3.1.11, p. 220. *)
Corollary norm_algebra_inverse_class_one (R : realType) (A : algebra R)
    (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (hcomplete : is_complete_metric_space (real_norm_metric_space hN))
    (F : A->A)
    (hF : forall x, partial_function_domain (algebra_inverse A) x ->
      is_two_sided_algebra_inverse x (F x)) :
  norm_class_one N N (partial_function_domain (algebra_inverse A)) F.
Proof.
exists (fun x=>algebra_inverse_linear_term (F x)).
exact (@norm_algebra_inverse_class_one_field R A N hN hM hcomplete F hF).
Qed.
