(** Federer (1969), 3.1.1, p. 210: invariant-ball and geometric
    increment estimates for the inverse-function iteration. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealNormUP InverseFunctionIterationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inverse_iteration_corrected_difference]: Federer
    3.1.1, p. 210 line 26, as corrected in the May 1987 erratum, p. 4:
    the next increment is g(u_n)-g(u_(n+1)), with this order of subtraction.
    The shift of indices here avoids natural-number predecessor notation. *)
Lemma inverse_iteration_corrected_difference (R : fieldType) (X : lmodType R)
    (g : X -> X) (y : X) (u : nat -> X) :
  is_inverse_function_iteration g y u -> forall n,
  u n.+2-u n.+1 = g (u n)-g (u n.+1).
Proof.
move=> hu n; rewrite (inverse_iteration_step hu n.+1) (inverse_iteration_step hu n).
have hsub : forall b c : X, y-b-(y-c) = c-b.
  by move=> b c; rewrite opprB addrCA addrAC subrr add0r.
exact: hsub.
Qed.

(** Source for [inverse_iteration_ball_bound]: the invariant-ball
    estimate in Federer 3.1.1, p. 210. The stronger finite-stage bound
    (1-c^n)r proves membership in the closed ball of radius r, including
    a target y on the boundary of the smaller closed ball. *)
Lemma inverse_iteration_ball_bound (R : realType) (X : lmodType R)
    (N : X -> R) (hN : is_real_norm N) (g : X -> X)
    (y : X) (u : nat -> X) (c r : R) :
  is_inverse_function_iteration g y u -> g 0 = 0 ->
  0 <= c < 1 -> 0 < r -> N y <= (1-c)*r ->
  (forall x z, N x <= r -> N z <= r -> N (g x-g z) <= c*N (x-z)) ->
  forall n, N (u n) <= (1-c^+n)*r /\ N (u n) <= r.
Proof.
move=> hu hg0 /andP [hc hc1] hr hy hg.
have hr0 := ltW hr.
have hzero : N 0 <= r by rewrite (real_seminorm_zero hN.1).
have main : forall n, N (u n) <= (1-c^+n)*r.
  elim=> [|n ih].
  - by rewrite (inverse_iteration_zero hu) (real_seminorm_zero hN.1) expr0 subrr mul0r.
  - have hcn : 0 <= c^+n by exact: exprn_ge0.
    have hn : N (u n) <= r by nra.
    have hgb := hg (u n) 0 hn hzero; rewrite hg0 !subr0 in hgb.
    have hbound : N (g (u n)) <= c*((1-c^+n)*r).
      apply: le_trans hgb _; apply: ler_wpM2l=> //.
    rewrite (inverse_iteration_step hu).
    apply: le_trans (real_seminorm_triangle hN.1 y (-g (u n))) _.
    rewrite (real_seminorm_negate hN.1).
    apply: le_trans (lerD hy hbound) _.
    rewrite exprS; by nra.
move=> n; have hh := main n; split=> //.
have hcn : 0 <= c^+n by exact: exprn_ge0.
by nra.
Qed.

(** Source for [inverse_iteration_geometric_increments]: the bound
    on successive increments in Federer 3.1.1, p. 210, with the corrected
    subtraction order from erratum p. 4, book p. 210 line 26. *)
Lemma inverse_iteration_geometric_increments (R : realType) (X : lmodType R)
    (N : X -> R) (hN : is_real_norm N) (g : X -> X)
    (y : X) (u : nat -> X) (c r : R) :
  is_inverse_function_iteration g y u -> g 0 = 0 ->
  0 <= c < 1 -> 0 < r -> N y <= (1-c)*r ->
  (forall x z, N x <= r -> N z <= r -> N (g x-g z) <= c*N (x-z)) ->
  forall n, N (u n.+1-u n) <= c^+n*N y.
Proof.
move=> hu hg0 hc hr hy hg.
have hball := @inverse_iteration_ball_bound R X N hN g y u c r hu hg0 hc hr hy hg.
elim=> [|n ih].
- by rewrite (inverse_iteration_step hu) (inverse_iteration_zero hu) hg0 !subr0 expr0 mul1r.
- rewrite (inverse_iteration_corrected_difference hu).
  have hb := hg (u n) (u n.+1) (hball n).2 (hball n.+1).2.
  rewrite [N (u n-u n.+1)](real_seminorm_subtract hN.1) in hb.
  apply: le_trans hb _; rewrite exprS -mulrA.
  apply: ler_wpM2l; first exact: (andP hc).1.
  exact ih.
Qed.
