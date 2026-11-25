(** Federer (1969), 3.2.13, p. 251: induction from
    beta_t(m,m)= 1 and the one-dimensional ratio gives the
    finite product for beta_t(n,m)^t. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp constructive_ereal.
From Federer Require Import ProjectionBeta ProjectionBetaDiagonal ProjectionBetaRatio RealPower RealPowerDivision.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [projection_beta_one_power_ratio]: the factor
    beta_t(m+j+1,1)^t/beta_t(j+1,1)^t in the
    inductive product of Federer 3.2.13, p. 251. *)
Definition projection_beta_one_power_ratio (R:realType) m (t:R) (ht:1<=t) j:R:=
  real_power (@projection_beta R (m+j).+1 1 (ltn0Sn (m+j)) t%:E) t/
    real_power (@projection_beta R j.+1 1 (ltn0Sn j) t%:E) t.

(** Source for [projection_beta_offset_product]: the finite
    product in Federer 3.2.13, p. 251, before substituting
    the already proved one-dimensional Gamma formula. The indices
    j= 0,...,k-1 correspond to the printed dimensions m+1,...,m+k. *)
Theorem projection_beta_offset_product (R:realType) m (hm:(0<m)%N) (t:R) (ht:1<=t) k:
  real_power (@projection_beta R (m+k) m (leq_addr k m) t%:E) t=
    \prod_(j<k) projection_beta_one_power_ratio m ht j.
Proof.
have htE:(1<=t%:E)%E by rewrite lee_fin.
have hDiag (hmm:(m<=m)%N):@projection_beta R m m hmm t%:E= 1.
  rewrite (@projection_beta_proof_irrelevant R m m hmm (leqnn m) t%:E).
  exact:projection_beta_diagonal ht.
elim:k=>[|k ih].
- rewrite big_ord0.
  have hBase:@projection_beta R (m+0) m (leq_addr 0 m) t%:E= 1.
    rewrite (@projection_beta_dimension_transport R (m+0) m m (leq_addr 0 m) (leqnn m) t%:E (addn0 m)).
    exact:projection_beta_diagonal ht.
  by rewrite hBase real_power_one_base.
- rewrite big_ord_recr /=.
  rewrite (@projection_beta_dimension_transport R (m+k.+1) (m+k).+1 m
    (leq_addr k.+1 m) (projection_offset_guard m k) t%:E (addnS m k))
    (projection_beta_offset_step hm k ht).
  have hL:=@projection_beta_positive R (m+k) m (leq_addr k m) t%:E htE.
  have hN:=@projection_beta_positive R (m+k).+1 1 (ltn0Sn (m+k)) t%:E htE.
  have hD:=@projection_beta_positive R k.+1 1 (ltn0Sn k) t%:E htE.
  rewrite real_power_product ?(ltW hL) ?(divr_ge0 (ltW hN) (ltW hD)) //
    real_power_division ?(ltW hN) // ih /projection_beta_one_power_ratio.
  by [].
Qed.
