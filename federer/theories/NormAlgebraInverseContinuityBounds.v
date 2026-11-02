(** Federer (1969), 3.1.11, p. 220:
    local estimates for the first differential of inversion.
    These support continuity in the full operator norm,
    including arbitrary Banach spaces. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom Bilinear AlgebraUP RealNormUP AlgebraInverseUP
  AlgebraInverseDifference NormAlgebraInverseBounds NormAlgebraInverseDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [algebra_inverse_linear_difference]:
    supporting algebraic expansion of the first inverse
    differential in Federer 3.1.11, p. 220. *)
Lemma algebra_inverse_linear_difference (K : fieldType) (A : algebra K)
    (v w u : A) :
  (algebra_inverse_linear_term w-algebra_inverse_linear_term v) u =
  -(alg_mul A (w-v) (alg_mul A u w)+
    alg_mul A v (alg_mul A u (w-v))).
Proof.
change (-alg_mul A w (alg_mul A u w)- -alg_mul A v (alg_mul A u v)=
  -(alg_mul A (w-v) (alg_mul A u w)+alg_mul A v (alg_mul A u (w-v)))).
by rewrite (bilBl (alg_bilinear A)) !(bilBr (alg_bilinear A))
  addrA subrK opprB opprK addrC.
Qed.

(** Source for [norm_algebra_inverse_difference_bound]:
    a local Lipschitz bound for inversion, supporting
    Federer 3.1.11, p. 220. Existence of the
    nearby inverse is supplied separately by the Neumann series. *)
Lemma norm_algebra_inverse_difference_bound (R : realType) (A : algebra R)
    (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (x v h w : A) (C : R) :
  is_two_sided_algebra_inverse x v -> is_two_sided_algebra_inverse (x+h) w ->
  0<C -> N v<=C -> 2*C*N h<= 1 ->
  N (w-v)<= 2*C^+2*N h.
Proof.
move=> hv hw hC hCv hs.
have hW := norm_algebra_inverse_near_bound hN hM hv hw hC hCv hs.
have hH0 := real_seminorm_nonnegative hN.1 h.
have hV0 := real_seminorm_nonnegative hN.1 v.
rewrite (algebra_inverse_perturbation_difference hv hw)
  (real_seminorm_negate hN.1).
have h1 := le_trans (hM h w) (ler_wpM2l hH0 hW).
have h2 := le_trans (hM v (alg_mul A h w)) (ler_wpM2l hV0 h1).
have h3 : N v*(N h*(2*C))<=C*(N h*(2*C)).
  apply: ler_wpM2r=> //; apply: mulr_ge0=> //.
  by apply: mulr_ge0; [exact: ler0n|exact: ltW hC].
have he : C*(N h*(2*C))= 2*C^+2*N h by ring.
apply: le_trans h2 _; by rewrite -he.
Qed.

(** Source for [norm_algebra_inverse_linear_difference_bound]:
    continuity of the inverse differential, supporting
    the infinite differentiability assertion in Federer
    3.1.11, p. 220. This estimate is uniform
    in the direction u and so controls the operator norm. *)
Lemma norm_algebra_inverse_linear_difference_bound (R : realType) (A : algebra R)
    (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (x v h w : A) (C : R) :
  is_two_sided_algebra_inverse x v -> is_two_sided_algebra_inverse (x+h) w ->
  0<C -> N v<=C -> 2*C*N h<= 1 ->
  forall u, N ((algebra_inverse_linear_term w-algebra_inverse_linear_term v) u)<=
    6*C^+3*N h*N u.
Proof.
move=> hv hw hC hCv hs u.
have hW := norm_algebra_inverse_near_bound hN hM hv hw hC hCv hs.
have hD := norm_algebra_inverse_difference_bound hN hM hv hw hC hCv hs.
have hC0 := ltW hC.
have hV0 := real_seminorm_nonnegative hN.1 v.
have hU0 := real_seminorm_nonnegative hN.1 u.
have hD0 := real_seminorm_nonnegative hN.1 (w-v).
have hH0 := real_seminorm_nonnegative hN.1 h.
have hW0 := real_seminorm_nonnegative hN.1 w.
rewrite algebra_inverse_linear_difference (real_seminorm_negate hN.1).
apply: le_trans (real_seminorm_triangle hN.1 _ _) _.
have h1 := le_trans (hM (w-v) (alg_mul A u w))
  (ler_wpM2l hD0 (hM u w)).
have h2 := le_trans (hM v (alg_mul A u (w-v)))
  (ler_wpM2l hV0 (hM u (w-v))).
have h3 : N (w-v)*(N u*N w)<=
    (2*C^+2*N h)*(N u*(2*C)).
  exact: ler_pM hD0 (mulr_ge0 hU0 hW0) hD (ler_wpM2l hU0 hW).
have h4 : N v*(N u*N (w-v))<=
    C*(N u*(2*C^+2*N h)).
  exact: ler_pM hV0 (mulr_ge0 hU0 hD0) hCv (ler_wpM2l hU0 hD).
have hsum := lerD (le_trans h1 h3) (le_trans h2 h4).
have he : (2*C^+2*N h)*(N u*(2*C))+C*(N u*(2*C^+2*N h))=
    6*C^+3*N h*N u by ring.
by rewrite he in hsum.
Qed.
