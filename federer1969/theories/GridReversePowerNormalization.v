(** Federer (1969), 3.2.38, p. 275: exact cancellation of
    the tube-radius powers after a side-vr source cube is selected. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [grid_reverse_power_normalization]: supporting each
    j<=m term of the normalized full Steiner sum in Federer 3.2.38,
    p. 275. Positive mesh ratio v and radius r justify cancellation;
    both zero exponents and the indispensable j=0 term remain. *)
Lemma grid_reverse_power_normalization (R:realType) (v r A:R) j m n:
  0<v ->0<r ->(j<=m)%N ->(m<=n)%N ->
  (v*r)^+j*(A*r)^+(n-j)/r^+(n-m)=
    (v*r)^+m*A^+(n-j)*(v^-1)^+(m-j).
Proof.
move=>hv hr hjm hmn.
have hjn:(j<=n)%N:=leq_trans hjm hmn.
have hRadiusProduct:r^+j*r^+(n-j)=r^+n by rewrite -exprD addnC subnK.
have hRadiusSplit:r^+n=r^+m*r^+(n-m) by rewrite -exprD addnC subnK.
have hRatioSplit:v^+m=v^+j*v^+(m-j) by rewrite -exprD addnC subnK.
have hrPositive:0<r^+(n-m):=exprn_gt0 _ hr.
have hvPositive:0<v^+(m-j):=exprn_gt0 _ hv.
have hrNonzero:r^+(n-m)!=0 by rewrite gt_eqF.
have hvNonzero:v^+(m-j)!=0 by rewrite gt_eqF.
rewrite !exprMn exprVn hRatioSplit.
have hLeft:
    v^+j*r^+j*(A^+(n-j)*r^+(n-j))/r^+(n-m)=
    (v^+j*A^+(n-j)*r^+m)*(r^+(n-m)*(r^+(n-m))^-1).
  have hShape:v^+j*r^+j*(A^+(n-j)*r^+(n-j))/r^+(n-m)=
      v^+j*A^+(n-j)*(r^+j*r^+(n-j))*(r^+(n-m))^-1 by ring.
  rewrite hShape hRadiusProduct hRadiusSplit; ring.
have hRight:(v^+j*v^+(m-j)*r^+m)*A^+(n-j)*(v^+(m-j))^-1=
    (v^+j*A^+(n-j)*r^+m)*(v^+(m-j)*(v^+(m-j))^-1) by ring.
by rewrite hLeft hRight !mulfV // !mulr1.
Qed.
