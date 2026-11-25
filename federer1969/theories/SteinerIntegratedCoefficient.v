(** Federer (1969), 3.2.35, p. 272:
    express the integrated radius coefficient
    in the printed final polynomial form. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp constructive_ereal ring.
From Federer Require Import ProjectionBeta SteinerTubePolynomial SteinerIndexedCoefficient EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [steiner_integrated_coefficient]: the
    m-th term equality in the final line
    of Federer 3.2.35, p. 272. The
    proved original-index alpha/beta identity and
    actual integral factor r^(n-m)/(n-m)
    give alpha(n-m)r^(n-m). All natural
    0<=m<=k, including both endpoints, remain. *)
Lemma steiner_integrated_coefficient (R:realType) k m (hmk:(m<=k)%N) (r:R):
  (2/ @projection_beta R k.+1 k (leqnSn k) 1)*
    euclidean_unit_ball_volume R (k-m)*
    (@projection_beta R k.+1 m (leq_trans hmk (leqnSn k)) 1 / @projection_beta R k m hmk 1)*
    (r^+(k-m).+1/(k-m).+1%:R)=
  euclidean_unit_ball_volume R (k.+1-m)*r^+(k.+1-m).
Proof.
have hDifference:(k.+1-m=(k-m).+1)%N by rewrite subSn.
have hBetaLow:(@projection_beta R k m hmk 1)!=0:=
  lt0r_neq0 (@projection_beta_positive R k m hmk 1 (lexx 1)).
have hBetaMain:(@projection_beta R k.+1 k (leqnSn k) 1)!=0:=
  lt0r_neq0 (@projection_beta_positive R k.+1 k (leqnSn k) 1 (lexx 1)).
have hNatural:((k-m).+1%:R:R)!=0 by rewrite pnatr_eq0.
have hAddNatural:((k-m)%:R+1:R)!=0 by rewrite natr1 pnatr_eq0.
have hReorder:
  (2/ @projection_beta R k.+1 k (leqnSn k) 1)*euclidean_unit_ball_volume R (k-m)*
    (@projection_beta R k.+1 m (leq_trans hmk (leqnSn k)) 1 / @projection_beta R k m hmk 1)*
    (r^+(k-m).+1/(k-m).+1%:R)=
  ((2*euclidean_unit_ball_volume R (k-m)*
    @projection_beta R k.+1 m (leq_trans hmk (leqnSn k)) 1)/
    ((k.+1-m)%:R* @projection_beta R k m hmk 1*
      @projection_beta R k.+1 k (leqnSn k) 1))*r^+(k.+1-m).
  rewrite hDifference !invfM; ring.
by rewrite hReorder steiner_indexed_coefficient.
Qed.
