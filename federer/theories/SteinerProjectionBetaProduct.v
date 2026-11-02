(** Federer (1969), 3.2.35, p. 272:
    the exact product of projection constants
    in the final coefficient calculation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp constructive_ereal ring.
From Federer Require Import ProjectionBeta ProjectionBetaZeroDegree ProjectionBetaRatio ProjectionBetaFirstGamma
  FullDimensionProjectionNorm GammaHalfSequences.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [projection_beta_two_dimensions_transport]:
    dimension equality bookkeeping supporting the
    zero-degree endpoints of the coefficient
    identity in Federer 3.2.35, p. 272.
    Only guard proof irrelevance is used. *)
Lemma projection_beta_two_dimensions_transport (R:realType) n n' m m'
    (h:(m<=n)%N) (h':(m'<=n')%N) t:
  n=n' ->m=m' ->@projection_beta R n m h t=@projection_beta R n' m' h' t.
Proof.
move=>hn hm; subst n'; subst m'; exact:projection_beta_proof_irrelevant.
Qed.

(** Source for [steiner_projection_beta_product]:
    supporting the last coefficient equality in
    Federer 3.2.35, p. 272, from the
    actual Gamma quotient of 3.2.13, p. 251.
    Put n=m+j+1. Cancellation gives the
    needed beta(n,m) beta(j+1,j)=
    beta(n-1,m) beta(n,n-1). The separate
    degree-zero and diagonal proofs retain all
    natural m,j, with no omitted endpoint. *)
Lemma steiner_projection_beta_product (R:realType) m j:
  @projection_beta R (m+j).+1 m (projection_offset_guard m j) 1*
    @projection_beta R j.+1 j (leqnSn j) 1=
  @projection_beta R (m+j) m (leq_addr j m) 1*
    @projection_beta R (m+j).+1 (m+j) (leqnSn (m+j)) 1.
Proof.
case:(posnP m)=>[->|hm].
- by rewrite !add0n !projection_beta_zero_degree // !mul1r.
case:(posnP j)=>[->|hj].
- have hUpper:=@projection_beta_two_dimensions_transport R (m+0).+1 m.+1 m m
    (projection_offset_guard m 0) (leqnSn m) 1 (congr1 S (addn0 m)) erefl.
  have hLower:=@projection_beta_two_dimensions_transport R (m+0) m m m
    (leq_addr 0 m) (leqnn m) 1 (addn0 m) erefl.
  have hMain:=@projection_beta_two_dimensions_transport R (m+0).+1 m.+1 (m+0) m
    (leqnSn (m+0)) (leqnSn m) 1 (congr1 S (addn0 m)) (addn0 m).
  by rewrite hUpper hLower hMain projection_beta_zero_degree // mulr1 equal_dimension_projection_beta // mul1r.
have hDiff:((m+j).+1-m=j.+1)%N by rewrite -addnS addKn.
have hDiffJ:(j.+1-j= 1)%N by rewrite -addn1 addKn.
have hDiffSum:((m+j).+1-(m+j)= 1)%N by rewrite -addn1 addKn.
have hSum:(0<m+j)%N:=leq_trans hm (leq_addr j m).
rewrite (@projection_beta_first_gamma_formula R (m+j).+1 m hm (projection_offset_guard m j))
  (@projection_beta_first_gamma_formula R j.+1 j hj (leqnSn j))
  (@projection_beta_first_gamma_formula R (m+j) m hm (leq_addr j m))
  (@projection_beta_first_gamma_formula R (m+j).+1 (m+j) hSum (leqnSn (m+j)))
  hDiff hDiffJ hDiffSum addKn.
have hNe i:gamma_half_sequence R i!=0:=lt0r_neq0 (gamma_half_sequence_positive R i).
field; by rewrite ?mulf_eq0 !(negbTE (hNe _)).
Qed.
