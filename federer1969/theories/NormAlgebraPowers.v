(** Federer (1969), 3.1.11, p. 220:
    geometric bounds for powers in a normed associative
    algebra. They support convergence of the inverse series. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import AlgebraUP AlgebraPowers RealNormUP NormMetric RecurrentContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_algebra_power_bound]: geometric
    norm bound for powers in the inverse series of
    Federer 3.1.11, p. 220. The unit is allowed
    to have any finite norm, including zero. *)
Lemma norm_algebra_power_bound (R : realType) (A : algebra R)
    (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (x : A) (c : R) :
  0<=c -> N x<=c -> forall n,
    N (@AlgebraPowers.algebra_power R A x n)<=c^+n*N (alg_one A).
Proof.
move=> hc hxc; elim=> [|n ih].
- by rewrite AlgebraPowers.algebra_power0 expr0 mul1r.
- change (N (alg_mul A x (@AlgebraPowers.algebra_power R A x n))<=c^+n.+1*N (alg_one A)).
  apply: le_trans (hM _ _) _.
  apply: le_trans (ler_wpM2l (real_seminorm_nonnegative hN.1 x) ih) _.
  rewrite exprS -mulrA.
  apply: ler_wpM2r; last exact hxc.
  exact: mulr_ge0 (exprn_ge0 n hc) (real_seminorm_nonnegative hN.1 _).
Qed.

(** Source for [norm_algebra_powers_vanish]: powers of
    an element with norm less than one tend to zero,
    supporting the inverse series in Federer 3.1.11,
    p. 220. The explicit c is any positive upper
    bound below one for the element's norm. *)
Lemma norm_algebra_powers_vanish (R : realType) (A : algebra R)
    (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (x : A) (c : R) :
  0<c< 1 -> N x<=c ->
  (fun n=>(@AlgebraPowers.algebra_power R A x n : real_norm_metric_space hN)) @ \oo -->
    (0 : real_norm_metric_space hN).
Proof.
move=> /andP [hc0 hc1] hxc W hW.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP
  (0 : real_norm_metric_space hN) W) hW.
have hq : 0<c< 1 by apply/andP.
have hunit := real_seminorm_nonnegative hN.1 (alg_one A).
have [k hk] := geometric_contraction_small hq hunit he.
exists k=> // n hkn; apply: hball.
change (N (0-@AlgebraPowers.algebra_power R A x n)<e).
rewrite sub0r (real_seminorm_negate hN.1).
apply: le_lt_trans (norm_algebra_power_bound hN hM (ltW hc0) hxc n) _.
apply: le_lt_trans _ hk.
apply: ler_wpM2r=> //.
have hh := ler_wiXn2l (ltW hc0) (ltW hc1) hkn.
exact hh.
Qed.
