(** Federer (1969), 4.1.12, p. 369: the
    explicit reciprocal-square masses and reciprocal-cube
    interval lengths have finite original numerical
    sums. Elementary telescoping and comparison supply
    the bounds; no external series theorem is imported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal lra ring.
From Federer Require Import NonnegativeSum NonnegativeRealSeriesTelescoping.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [reciprocal_power_series_weight]: the
    original k^(-p) with k>=1, with
    formal index n denoting k=n+1,
    supporting Federer 4.1.12, p. 369. *)
Definition reciprocal_power_series_weight (R:realType) p n:R:=((n.+1)%:R)^-1^+p.

(** Source for [reciprocal_power_series_weight_positive]:
    every original reciprocal-power summand is
    positive, supporting Federer 4.1.12, p. 369. *)
Lemma reciprocal_power_series_weight_positive (R:realType) p n:
  0<reciprocal_power_series_weight R p n.
Proof. rewrite /reciprocal_power_series_weight;apply:exprn_gt0;by rewrite invr_gt0 ltr0n. Qed.

(** Source for [reciprocal_square_series_telescoping_step]:
    k^(-2)<=2/k-2/(k+1) for k>=1,
    supporting the finite mass series in
    Federer 4.1.12, p. 369. *)
Lemma reciprocal_square_series_telescoping_step (R:realType) n:
  reciprocal_power_series_weight R 2%N n<=2/(n.+1)%:R-2/(n.+2)%:R.
Proof.
pose x:R:=(n.+1)%:R.
have hx:0<x by rewrite /x ltr0n.
have hx1:1<=x by rewrite /x ler1n.
have hx0:x!=0 by rewrite gt_eqF.
have hNext:0<x+1 by lra.
have hNext0:x+1!=0 by rewrite gt_eqF.
have hIdentity:2/x-2/(x+1)-x^-1^+2=(x-1)/(x^+2*(x+1)).
  field;apply/andP;split;apply/eqP=>hZero.
  - have hPos:=hx;rewrite /x -natr1 in hPos;lra.
  - have hPos:=hx;rewrite /x -natr1 in hPos;lra.
have hNonnegative:0<=(x-1)/(x^+2*(x+1)).
  apply:divr_ge0;first by rewrite subr_ge0.
  exact:mulr_ge0 (sqr_ge0 x) (ltW hNext).
rewrite -hIdentity in hNonnegative.
change (is_true (x^-1^+2<=2/x-2/(n.+2)%:R)).
have hNextCast:((n.+2)%:R:R)=x+1 by rewrite /x natr1.
rewrite hNextCast;by move:hNonnegative;rewrite subr_ge0.
Qed.

(** Source for [reciprocal_cube_le_square]: the
    original k^(-3) is at most k^(-2)
    for k>=1, supporting the compact support
    sum in Federer 4.1.12, p. 369. *)
Lemma reciprocal_cube_le_square (R:realType) n:
  reciprocal_power_series_weight R 3%N n<=reciprocal_power_series_weight R 2%N n.
Proof.
pose x:R:=(n.+1)%:R.
have hx:0<x by rewrite /x ltr0n.
have hx1:1<=x by rewrite /x ler1n.
have hx0:x!=0 by rewrite gt_eqF.
have hInv:0<x^-1 by rewrite invr_gt0.
have hCancel:x*x^-1= 1 by rewrite mulfV.
have hInvBound:x^-1<=1.
  rewrite -[1]invr1 (@lef_pV2 R x 1 hx (@ltr01 R)).
  exact:hx1.
change (is_true (x^-1^+3<=x^-1^+2)).
rewrite exprS.
have h:=ler_wpM2r (sqr_ge0 x^-1) hInvBound.
by rewrite mul1r in h.
Qed.

(** Source for [reciprocal_square_series_sum_bound]:
    the original sum of k^(-2), k>=1,
    is at most two and hence finite,
    supporting Federer 4.1.12, p. 369. *)
Theorem reciprocal_square_series_sum_bound (R:realType):
  (nonnegative_sum setT (fun n=>(reciprocal_power_series_weight R 2%N n)%:E)<=(2:R)%:E)%E.
Proof.
have hTail n:0<=(2:R)/(n.+1)%:R.
  apply:divr_ge0;by rewrite ler0n.
have h:=@nonnegative_real_series_telescoping_bound R (reciprocal_power_series_weight R 2%N)
  (fun n=>2/(n.+1)%:R) (fun n=>ltW (reciprocal_power_series_weight_positive R 2%N n))
  hTail (@reciprocal_square_series_telescoping_step R).
by rewrite divr1 in h.
Qed.

(** Source for [reciprocal_cube_series_sum_bound]:
    the original sum of k^(-3), k>=1,
    is at most two and hence finite,
    supporting the compact interval in Federer
    4.1.12, p. 369. *)
Theorem reciprocal_cube_series_sum_bound (R:realType):
  (nonnegative_sum setT (fun n=>(reciprocal_power_series_weight R 3%N n)%:E)<=(2:R)%:E)%E.
Proof.
apply:le_trans (reciprocal_square_series_sum_bound R).
apply:nonnegative_sum_mono=>n _;rewrite lee_fin;exact:reciprocal_cube_le_square.
Qed.

(** Source for [reciprocal_square_series_finite]: the
    printed reciprocal-square sum is finite,
    as used in Federer 4.1.12, p. 369. *)
Corollary reciprocal_square_series_finite (R:realType):
  (nonnegative_sum setT (fun n=>(reciprocal_power_series_weight R 2%N n)%:E)< +oo)%E.
Proof. exact:le_lt_trans (reciprocal_square_series_sum_bound R) (ltry _). Qed.

(** Source for [reciprocal_cube_series_finite]: the
    printed reciprocal-cube sum is finite,
    as used in Federer 4.1.12, p. 369. *)
Corollary reciprocal_cube_series_finite (R:realType):
  (nonnegative_sum setT (fun n=>(reciprocal_power_series_weight R 3%N n)%:E)< +oo)%E.
Proof. exact:le_lt_trans (reciprocal_cube_series_sum_bound R) (ltry _). Qed.
