(** Federer (1969), 3.2.35, p. 272:
    express the proved scalar coefficient identity
    in the original m=0,...,k induction range. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp constructive_ereal.
From Federer Require Import ProjectionBeta ProjectionBetaRatio SteinerProjectionBetaProduct
  SteinerCoefficientIdentity EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [steiner_indexed_coefficient]: the
    exact scalar coefficient in the last line
    of Federer 3.2.35, p. 272, with
    n=k+1 and every 0<=m<=k. The proved
    offset identity is transported by actual
    dimension equalities, preserving each dimension
    guard without dependent rewriting. *)
Lemma steiner_indexed_coefficient (R:realType) k m (hmk:(m<=k)%N):
  (2*euclidean_unit_ball_volume R (k-m)*
    @projection_beta R k.+1 m (leq_trans hmk (leqnSn k)) 1)/
  ((k.+1-m)%:R* @projection_beta R k m hmk 1*
    @projection_beta R k.+1 k (leqnSn k) 1)=
  euclidean_unit_ball_volume R (k.+1-m).
Proof.
have hDim:(m+(k-m)=k)%N:=subnKC hmk.
have hSuccessor:((m+(k-m)).+1=k.+1)%N:=congr1 S hDim.
have hDifference:(k.+1-m=(k-m).+1)%N by rewrite subSn.
have hUpper:=@projection_beta_two_dimensions_transport R (m+(k-m)).+1 k.+1 m m
  (projection_offset_guard m (k-m)) (leq_trans hmk (leqnSn k)) 1 hSuccessor erefl.
have hLower:=@projection_beta_two_dimensions_transport R (m+(k-m)) k m m
  (leq_addr (k-m) m) hmk 1 hDim erefl.
have hMain:=@projection_beta_two_dimensions_transport R (m+(k-m)).+1 k.+1 (m+(k-m)) k
  (leqnSn (m+(k-m))) (leqnSn k) 1 hSuccessor hDim.
have hCoefficient:=steiner_coefficient_quotient_identity R m (k-m).
by rewrite hUpper hLower hMain -hDifference in hCoefficient.
Qed.
