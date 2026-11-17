(** Elementary coefficient support for Federer (1969), 3.2.45,
    p. 280: the intrinsic product convolution for a cube is bounded
    by the binomial expansion with a common degree constant. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_filtered_degree_bound]: supporting the
    single admissible coefficient in the inner product sum of
    Federer 3.2.45, p. 280. Empty degree fibres contribute zero;
    the statement keeps both zero-dimensional coordinate blocks. *)
Lemma finite_filtered_degree_bound (R : realType) m n k
    (b : 'I_n.+1 -> R) (G D : R) :
  0 <= G -> 0 <= D ->
  (forall j : 'I_n.+1, (k <= j)%N -> b j <= G * D^+(j-k)) ->
  forall i : 'I_m.+1,
    \sum_(j : 'I_n.+1 | (i+j == m+k)%N) b j <= G * D^+(m-i).
Proof.
move=> hG hD hB i.
case: (pselect (exists j : 'I_n.+1, (i+j = m+k)%N))=> [[j0 hIndex]|hEmpty].
- have hPred (j : 'I_n.+1) : (i+j == m+k)%N = (j == j0).
    by rewrite -hIndex eqn_add2l -val_eqE.
  under eq_bigl do rewrite hPred.
  rewrite big_pred1_eq.
  have hIM : (i <= m)%N by have := ltn_ord i; rewrite ltnS.
  have hJ : (val j0 = m-i+k)%N.
    have hSum : (i+j0 == i+(m-i+k))%N.
      by rewrite addnA (subnKC hIM) hIndex eqxx.
    by move: hSum; rewrite eqn_add2l=> /eqP.
  have hKJ : (k <= j0)%N by rewrite hJ leq_addl.
  have h := hB j0 hKJ.
  by rewrite hJ addnK in h.
- rewrite big1; last first.
    move=> j /eqP hJ; exfalso; apply: hEmpty; by exists j.
  apply: mulr_ge0 hG _; exact: exprn_ge0.
Qed.

(** Source for [finite_binomial_convolution_bound]: the finite
    binomial step in the cube-product bound of Federer 3.2.45,
    p. 280. All coefficients are arbitrary real numbers subject
    only to the stated degree bounds; the geometric application
    supplies these from the original bounded convex set. *)
Lemma finite_binomial_convolution_bound (R : realType) m n k
    (b : 'I_n.+1 -> R) (G D s : R) :
  0 <= G -> 0 <= D -> 0 <= s ->
  (forall j : 'I_n.+1, (k <= j)%N -> b j <= G * D^+(j-k)) ->
  \sum_(i : 'I_m.+1) \sum_(j : 'I_n.+1 | (i+j == m+k)%N)
      ('C(m,i)%:R * s^+i) * b j <= G * (s+D)^+m.
Proof.
move=> hG hD hS hB.
have hSum :
    \sum_(i : 'I_m.+1) \sum_(j : 'I_n.+1 | (i+j == m+k)%N)
      ('C(m,i)%:R * s^+i) * b j <=
    \sum_(i : 'I_m.+1) ('C(m,i)%:R * s^+i) * (G * D^+(m-i)).
  apply: ler_sum=> i _.
  rewrite -mulr_sumr.
  apply: ler_wpM2l; first by apply: mulr_ge0; [exact: ler0n | exact: exprn_ge0].
  exact: (@finite_filtered_degree_bound R m n k b G D hG hD hB i).
have hPolynomial :
    (\sum_(i : 'I_m.+1) ('C(m,i)%:R * s^+i) * (G * D^+(m-i))) = G * (s+D)^+m.
  rewrite addrC exprDn mulr_sumr.
  apply: eq_bigr=> i _.
  rewrite -mulr_natl; ring.
by rewrite hPolynomial in hSum.
Qed.
