(** Federer (1969), 3.2.13, p. 251: specialize the
    projection-constant ratio from 2.7.16(6), p. 139,
    to one removed dimension. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp constructive_ereal.
From Federer Require Import ProjectionBeta ProjectionConstantNorms OrthogonalProjectionConstants
  OrthogonalWedgeIntegrals ExteriorDiameterUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [projection_beta_proof_irrelevant]: bookkeeping
    for repeated dimension guards in the projection constants of
    Federer 3.2.13, p. 251. *)
Lemma projection_beta_proof_irrelevant (R:realType) n m (h1 h2:(m<=n)%N) t:
  @projection_beta R n m h1 t=@projection_beta R n m h2 t.
Proof. by have ->:h1=h2:=Prop_irrelevance _ _. Qed.

(** Source for [projection_beta_dimension_transport]: equality of
    ambient dimensions preserves the projection constant, supporting
    the induction indexing in Federer 3.2.13, p. 251. *)
Lemma projection_beta_dimension_transport (R:realType) n n' m
    (h1:(m<=n)%N) (h2:(m<=n')%N) t:
  n=n' ->@projection_beta R n m h1 t=@projection_beta R n' m h2 t.
Proof.
move=>he; move:h2; rewrite -he=>h2; exact:projection_beta_proof_irrelevant.
Qed.

(** Source for [projection_offset_guard]: the dimension guard
    for one induction step in Federer 3.2.13, p. 251. *)
Lemma projection_offset_guard m k:(m<=(m+k).+1)%N.
Proof. exact:leq_trans (leq_addr k m) (leqnSn (m+k)). Qed.

(** Source for [projection_beta_offset_step]: the displayed
    ratio beta_t(n,m)/beta_t(n-1,m)=beta_t(n,1)/beta_t(n-m,1),
    Federer 3.2.13, p. 251, with n=(m+k)+1. All
    dimension guards are proved and all divisors are positive. *)
Lemma projection_beta_offset_step (R:realType) m (hm:(0<m)%N) k (t:R):
  1<=t ->
  @projection_beta R (m+k).+1 m (projection_offset_guard m k) t%:E=
    @projection_beta R (m+k) m (leq_addr k m) t%:E *
    (@projection_beta R (m+k).+1 1 (ltn0Sn (m+k)) t%:E /
      @projection_beta R k.+1 1 (ltn0Sn k) t%:E).
Proof.
move=>ht.
pose h2:=real_exterior_two_nonzero R.
have ht0:0<t:=lt_le_trans ltr01 ht.
have htE:(1<=t%:E)%E by rewrite lee_fin.
have hDim:(m+1<=(m+k).+1)%N by rewrite addn1 ltnS; exact:leq_addr.
have hDiff:((m+k).+1-m=k.+1)%N by rewrite -addnS addKn.
have hUpper:=@projection_beta_specification R (m+k).+1 m (projection_offset_guard m k) t%:E htE.
have hLower:is_projection_constant h2 t ((m+k).+1-1) m
    (@projection_beta R (m+k) m (leq_addr k m) t%:E).
  rewrite subn1 /=; exact:projection_beta_specification htE.
have hOne:=@projection_beta_specification R (m+k).+1 1 (ltn0Sn (m+k)) t%:E htE.
have hSmall:is_projection_constant h2 t ((m+k).+1-m) 1
    (@projection_beta R k.+1 1 (ltn0Sn k) t%:E).
  rewrite hDiff; exact:projection_beta_specification htE.
have hRatio:=@projection_constant_ratio R h2 t (m+k).+1 m 1
  (@projection_beta R (m+k).+1 m (projection_offset_guard m k) t%:E)
  (@projection_beta R (m+k) m (leq_addr k m) t%:E)
  (@projection_beta R (m+k).+1 1 (ltn0Sn (m+k)) t%:E)
  (@projection_beta R k.+1 1 (ltn0Sn k) t%:E)
  ht0 hDim hUpper hLower hOne hSmall.
have hPositive:=@projection_beta_positive R (m+k) m (leq_addr k m) t%:E htE.
have hCancel:=congr1 (fun v:R=>v* @projection_beta R (m+k) m (leq_addr k m) t%:E) hRatio.
rewrite divfK ?gt_eqF // in hCancel.
by rewrite mulrC in hCancel.
Qed.
