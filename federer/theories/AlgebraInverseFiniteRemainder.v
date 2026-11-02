(** Federer (1969), 3.1.11, p. 220:
    the inverse series has an exact finite
    remainder. Its norm estimate justifies the
    printed higher differential formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import AlgebraUP Bilinear AlgebraPowers AlgebraGeometricSum
  AlgebraInverseUP RealNormUP NormAlgebraInverseBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [algebra_inverse_finite_remainder]:
    the exact remainder after n terms
    of the inverse series, supporting the
    permutation formula in Federer 3.1.11,
    p. 220. The algebra need
    not be commutative; n= 0 is included. *)
Theorem algebra_inverse_finite_remainder (K : fieldType) (A : algebra K)
    (x v h w : A) n :
  is_two_sided_algebra_inverse x v ->
  is_two_sided_algebra_inverse (x+h) w ->
  w-alg_mul A (algebra_geometric_sum (-alg_mul A v h) n) v=
    alg_mul A (@AlgebraPowers.algebra_power K A (-alg_mul A v h) n) w.
Proof.
move=>[hxv hvx] [hxhw hwhx].
pose u := -alg_mul A v h.
have he : alg_mul A (alg_one A-u) w=v.
  have hh : alg_mul A v (x+h)=alg_one A-u.
    by rewrite (bilDr (alg_bilinear A)) hvx /u opprK.
  by rewrite -hh -alg_assoc hxhw alg_unitr.
have hs : alg_mul A (algebra_geometric_sum u n) v=
    w-alg_mul A (@AlgebraPowers.algebra_power K A u n) w.
  rewrite -{1}he alg_assoc algebra_geometric_sum_right.
  by rewrite (bilBl (alg_bilinear A)) alg_unitl.
change (w-alg_mul A (algebra_geometric_sum u n) v=alg_mul A (@AlgebraPowers.algebra_power K A u n) w).
by rewrite hs opprB addrCA subrr addr0.
Qed.

(** Source for [norm_algebra_power_product_bound]:
    a power followed by a fixed factor
    is bounded without inserting the norm
    of the unit, supporting Federer 3.1.11,
    p. 220, including the zero algebra. *)
Lemma norm_algebra_power_product_bound (R : realType) (A : algebra R)
    (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (u w : A) n :
  N (alg_mul A (@AlgebraPowers.algebra_power R A u n) w)<=(N u)^+n*N w.
Proof.
elim:n=>[|n ih].
- by rewrite AlgebraPowers.algebra_power0 alg_unitl expr0 mul1r.
- change (N (alg_mul A (alg_mul A u (@AlgebraPowers.algebra_power R A u n)) w)<=(N u)^+n.+1*N w).
  rewrite -alg_assoc; apply: le_trans (hM _ _) _.
  have hh := ler_wpM2l (real_seminorm_nonnegative hN.1 u) ih.
  by rewrite exprS -mulrA.
Qed.

(** Source for [norm_algebra_inverse_finite_remainder_bound]:
    the remainder after n terms is
    bounded by 2 C (C ||h||)^n
    for sufficiently small h, supporting the
    higher inverse differential in Federer 3.1.11,
    p. 220. Only the displayed
    inverses are assumed to exist. *)
Theorem norm_algebra_inverse_finite_remainder_bound (R : realType)
    (A : algebra R) (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (x v h w : A) (C : R) n :
  is_two_sided_algebra_inverse x v ->
  is_two_sided_algebra_inverse (x+h) w ->
  0<C -> N v<=C -> 2*C*N h<= 1 ->
  N (w-alg_mul A (algebra_geometric_sum (-alg_mul A v h) n) v)
    <=(C*N h)^+n*(2*C).
Proof.
move=>hv hw hC hCv hs.
rewrite (algebra_inverse_finite_remainder n hv hw).
apply: le_trans (norm_algebra_power_product_bound hN hM _ _ n) _.
have hh0 := real_seminorm_nonnegative hN.1 h.
have hu0 := real_seminorm_nonnegative hN.1 (-alg_mul A v h).
have hu : N (-alg_mul A v h)<=C*N h.
  rewrite (real_seminorm_negate hN.1).
  exact: le_trans (hM _ _) (ler_wpM2r hh0 hCv).
have hp := lerXn2r n hu0 (mulr_ge0 (ltW hC) hh0) hu.
have hW := norm_algebra_inverse_near_bound hN hM hv hw hC hCv hs.
apply: le_trans (ler_wpM2l (exprn_ge0 n hu0) hW) _.
exact (ler_wpM2r (mulr_ge0 (ler0n R 2) (ltW hC)) hp).
Qed.
