(** Federer (1969), 3.2.36, p. 273:
    the whole positive-distance level polynomial
    has the differentiated Steiner coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp constructive_ereal ring.
From Federer Require Import ProjectionBeta ProjectionBetaRatio SteinerProjectionBetaProduct
  SteinerCoefficientIdentity EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [steiner_distance_level_coefficient]:
    supporting the level-mass substitution in
    the product calculation of Federer 3.2.36,
    p. 273. The actual coefficient obtained
    by Cauchy and repeated projection is
    (n-m)alpha(n-m), as printed. This is
    proved from 3.2.35's actual Gamma and
    unit-ball coefficient identities, without
    differentiating an integral only almost
    everywhere or assuming a new level formula. *)
Lemma steiner_distance_level_coefficient (R:realType) k m (hmk:(m<=k)%N):
  (2/ @projection_beta R k.+1 k (leqnSn k) 1)*euclidean_unit_ball_volume R (k-m)*
    (@projection_beta R k.+1 m (leq_trans hmk (leqnSn k)) 1 /
      @projection_beta R k m hmk 1)=
  (k.+1-m)%:R*euclidean_unit_ball_volume R (k.+1-m).
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
have hProduct:=steiner_coefficient_product_identity R m (k-m).
rewrite hUpper hLower hMain -hDifference in hProduct.
have hDenPositive:0<(@projection_beta R k m hmk 1*
    @projection_beta R k.+1 k (leqnSn k) 1).
  apply:mulr_gt0.
  - exact:(@projection_beta_positive R k m hmk 1 (lexx 1)).
  - exact:(@projection_beta_positive R k.+1 k (leqnSn k) 1 (lexx 1)).
have hDenNonzero:(@projection_beta R k m hmk 1*
    @projection_beta R k.+1 k (leqnSn k) 1)!=0 by rewrite gt_eqF.
have hReorder (a b c e:R):(2/e)*a*(c/b)=(2*a*c)/(b*e).
  rewrite !invfM; ring.
have hCancel (a b c:R):b*c!=0 ->(a*b*c)/(b*c)=a.
  move=>hbc; by rewrite -[a*b*c]mulrA (mulfK hbc).
by rewrite hReorder hProduct hCancel //.
Qed.
