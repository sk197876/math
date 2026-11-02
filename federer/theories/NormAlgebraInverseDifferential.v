(** Federer (1969), 3.1.11, p. 220:
    the first differential of inversion is the map
    S to -T^(-1) S T^(-1). The domain is exactly
    the set of elements with a two-sided inverse. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra ring.
From Federer Require Import Hom Bilinear AlgebraUP RealNormUP NormMetric
  CompleteMetricUP PartialFunctionUP AlgebraInverseUP AlgebraInverse
  NormDifferentialUP NormAlgebraInverseOpen NormAlgebraInverseBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [algebra_inverse_linear_term]: the degree-one
    instance of the displayed permutation formula for inversion,
    Federer 3.1.11, p. 220. This is an algebraic linear map;
    its continuity is proved separately. *)
Definition algebra_inverse_linear_term (K : fieldType) (A : algebra K)
    (v : A) : Hom A A.
Proof.
apply: (@HomMap K A A (fun h=> -alg_mul A v (alg_mul A h v))).
apply/asboolP=> a h k.
by rewrite (bilDl (alg_bilinear A)) (bilZl (alg_bilinear A))
  (bilDr (alg_bilinear A)) (bilZr (alg_bilinear A)) opprD scalerN.
Defined.

(** Source for [algebra_inverse_linear_term_bounded]:
    continuity of the inverse differential, Federer 3.1.11,
    p. 220, follows from the norm inequality for composition. *)
Lemma algebra_inverse_linear_term_bounded (R : realType) (A : algebra R)
    (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y) (v : A) :
  norm_bounded_linear N N (algebra_inverse_linear_term v).
Proof.
exists (N v*N v); split.
- exact: mulr_ge0 (real_seminorm_nonnegative hN.1 v)
    (real_seminorm_nonnegative hN.1 v).
- move=> h; change (N (-alg_mul A v (alg_mul A h v))<=N v*N v*N h).
  rewrite (real_seminorm_negate hN.1).
  apply: le_trans (hM v (alg_mul A h v)) _.
  have hh := ler_wpM2l (real_seminorm_nonnegative hN.1 v) (hM h v).
  by rewrite [N h*N v]mulrC mulrA in hh.
Qed.

(** Source for [norm_algebra_inverse_differential]: the
    first derivative of the inversion operator in Federer
    3.1.11, p. 220. A total representative is constrained
    only on the exact inverse domain; no inverse is assigned
    or required outside that domain. The quadratic bound
    proves differentiability rather than assuming it. *)
Theorem norm_algebra_inverse_differential (R : realType) (A : algebra R)
    (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (hcomplete : is_complete_metric_space (real_norm_metric_space hN))
    (F : A->A)
    (hF : forall x, partial_function_domain (algebra_inverse A) x ->
      is_two_sided_algebra_inverse x (F x)) (x : A) :
  partial_function_domain (algebra_inverse A) x ->
  has_norm_differential N N (partial_function_domain (algebra_inverse A))
    F x (algebra_inverse_linear_term (F x)).
Proof.
move=> hx.
have hv := hF x hx.
constructor.
- exact (@norm_algebra_inverse_domain_interior R A N hN hM hcomplete x (F x) hv).
- exact (algebra_inverse_linear_term_bounded hN hM (F x)).
- move=> e he.
  pose C := N (F x)+1.
  pose P := 2*C^+3+1.
  have hNv := real_seminorm_nonnegative hN.1 (F x).
  have hC : 0<C by rewrite /C; lra.
  have hCv : N (F x)<=C by rewrite /C; lra.
  have hC3 : 0<C^+3 by exact: exprn_gt0.
  have hP : 0<P by rewrite /P; nra.
  have h2C : 0< 2*C by nra.
  exists (Num.min ((2*C)^-1) (e/P)); split.
  + by rewrite lt_min invr_gt0 h2C divr_gt0.
  + move=> h hxh; rewrite lt_min=> /andP [hh hs].
    have hH0 := real_seminorm_nonnegative hN.1 h.
    have hsmall : 2*C*N h<= 1.
      apply: ltW; move: hh.
      by rewrite -div1r ltr_pdivlMr // mulrC.
    have hscale : P*N h<e.
      by move: hs; rewrite ltr_pdivlMr // mulrC.
    have hcoeff : 2*C^+3*N h<=e by rewrite /P in hscale; nra.
    have hbound := norm_algebra_inverse_quadratic_bound
      hN hM hv (hF (x+h) hxh) hC hCv hsmall.
    change (N (F (x+h)-F x- -alg_mul A (F x) (alg_mul A h (F x)))<=e*N h).
    rewrite opprK.
    apply: le_trans hbound _.
    have hlast := ler_wpM2r hH0 hcoeff.
    by rewrite expr2 mulrA.
Qed.
