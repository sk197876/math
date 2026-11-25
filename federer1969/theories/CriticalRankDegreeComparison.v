(** Federer (1969), 3.4.3, pp. 316–317: compare
    the critical-image degrees of all original rank strata. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_rank_degree_nonnegative]: the degree
    nu+(m-nu)/k in 3.4.3, p. 316, belongs
    to the nonnegative real degrees of 2.10.2. Natural
    dimensions and the positive class order suffice. *)
Lemma critical_rank_degree_nonnegative (R:realType) m nu k:
  (1<=k)%N ->0<=(nu%:R+(m-nu)%:R/k%:R:R).
Proof.
move=>hk;apply:addr_ge0;first exact:ler0n.
apply:divr_ge0;exact:ler0n.
Qed.

(** Source for [critical_rank_degree_monotone]: the degree
    r+(m-r)/k of a lower rank stratum is at most
    nu+(m-nu)/k for r<=nu and k>=1. This
    supplies the rank-stratum assembly implicit in the proof of
    3.4.3, p. 317, including equality at class one. *)
Lemma critical_rank_degree_monotone (R:realType) m r nu k:
  (r<=nu)%N ->(nu<=m)%N ->(1<=k)%N ->
  (r%:R+(m-r)%:R/k%:R:R)<=nu%:R+(m-nu)%:R/k%:R.
Proof.
move=>hR hNu hk.
have hRM:(r<=m)%N:=leq_trans hR hNu.
have hK:(0<(k%:R:R)) by rewrite ltr0n;exact:leq_trans (leqnn 1) hk.
have hKOne:(1:R)<=k%:R.
  change (is_true (((1%N)%:R:R)<=k%:R));by rewrite ler_nat.
have hRNu:(r%:R:R)<=nu%:R by rewrite ler_nat.
have hDifference:0<=(nu%:R:R)-r%:R by rewrite subr_ge0.
have hClass:0<=(k%:R:R)-1 by rewrite subr_ge0.
have hProduct:=mulr_ge0 hDifference hClass.
rewrite !natrB //.
have hZero:(k%:R:R)!=0 by rewrite gt_eqF.
have hLeft:((r%:R+(m%:R-r%:R)/k%:R)*k%:R:R)= r%:R*k%:R+(m%:R-r%:R)
  by rewrite mulrDl divfK.
have hRight:((nu%:R+(m%:R-nu%:R)/k%:R)*k%:R:R)= nu%:R*k%:R+(m%:R-nu%:R)
  by rewrite mulrDl divfK.
rewrite -(ler_pM2r hK) hLeft hRight;by nra.
Qed.
