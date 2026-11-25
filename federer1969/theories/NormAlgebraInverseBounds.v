(** Federer (1969), 3.1.11, p. 220:
    uniform local bounds for inverses and the quadratic
    remainder used to differentiate inversion. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import AlgebraUP RealNormUP AlgebraInverseUP AlgebraInverseDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_algebra_inverse_near_bound]:
    nearby inverses have a uniform finite norm bound,
    supporting the inverse derivative in Federer 3.1.11,
    p. 220. Inverse existence is not assumed outside
    the two explicit inverse hypotheses. *)
Lemma norm_algebra_inverse_near_bound (R : realType) (A : algebra R)
    (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (x v h w : A) (C : R) :
  is_two_sided_algebra_inverse x v -> is_two_sided_algebra_inverse (x+h) w ->
  0<C -> N v<=C -> 2*C*N h<= 1 -> N w<= 2*C.
Proof.
move=> hv hw hC hCv hsmall.
have hd := algebra_inverse_perturbation_difference hv hw.
have hid : w=v-alg_mul A v (alg_mul A h w).
  by rewrite -[LHS](subrK v w) hd addrC.
have ht := real_seminorm_triangle hN.1 v (-alg_mul A v (alg_mul A h w)).
rewrite -hid (real_seminorm_negate hN.1) in ht.
have hprod := le_trans (hM v (alg_mul A h w))
  (ler_wpM2l (real_seminorm_nonnegative hN.1 v) (hM h w)).
have hV0 := real_seminorm_nonnegative hN.1 v.
have hH0 := real_seminorm_nonnegative hN.1 h.
have hW0 := real_seminorm_nonnegative hN.1 w.
have hupper : N v*(N h*N w)<=C*N h*N w.
  rewrite -mulrA; exact (ler_wpM2r (mulr_ge0 hH0 hW0) hCv).
have hsum := le_trans ht (lerD hCv (le_trans hprod hupper)).
have hs := ler_wpM2r hW0 hsmall.
nra.
Qed.

(** Source for [norm_algebra_inverse_quadratic_bound]:
    a quadratic norm bound for the inverse remainder,
    supporting its first derivative in Federer 3.1.11,
    p. 220. The constant is finite and independent
    of sufficiently small perturbations. *)
Lemma norm_algebra_inverse_quadratic_bound (R : realType) (A : algebra R)
    (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (x v h w : A) (C : R) :
  is_two_sided_algebra_inverse x v -> is_two_sided_algebra_inverse (x+h) w ->
  0<C -> N v<=C -> 2*C*N h<= 1 ->
  N (w-v+alg_mul A v (alg_mul A h v))<= 2*C^+3*(N h)^+2.
Proof.
move=> hv hw hC hCv hs.
have hW := norm_algebra_inverse_near_bound hN hM hv hw hC hCv hs.
have hH0 := real_seminorm_nonnegative hN.1 h.
have hC0 := ltW hC.
have hvb y : N (alg_mul A v y)<=C*N y.
  apply: le_trans (hM v y) _.
  exact (ler_wpM2r (real_seminorm_nonnegative hN.1 y) hCv).
rewrite (algebra_inverse_quadratic_remainder hv hw).
have h1 := le_trans (hM h w) (ler_wpM2l hH0 hW).
have h2 := le_trans (hvb (alg_mul A h w)) (ler_wpM2l hC0 h1).
have h3 := le_trans (hM h (alg_mul A v (alg_mul A h w))) (ler_wpM2l hH0 h2).
have h4 := le_trans (hvb (alg_mul A h (alg_mul A v (alg_mul A h w))))
  (ler_wpM2l hC0 h3).
have heq : C*(N h*(C*(N h*(2*C))))= 2*C^+3*(N h)^+2 by ring.
by rewrite heq in h4.
Qed.
