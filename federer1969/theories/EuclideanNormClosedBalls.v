(** Federer (1969), 4.1.2, p. 347: the
    original norm balls have their actual Lebesgue
    mass and compactness. These adapters identify the
    norm presentation with the already proved Euclidean
    closed-ball laws of 2.8.8 and 2.7.16. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness FiniteNormEquivalence MetricClosedBalls EuclideanClosedBallGrowth EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanNormClosedBalls.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NT := (real_norm_metric_space hN).
Local Notation IT := (inner_metric_space (@euclidean_inner_productP R n)).

(** Source for [euclidean_norm_closed_ballE]: the ball
    B(x,epsilon) in the smoothing estimate, Federer
    4.1.2, p. 347, is the original norm ball. *)
Lemma euclidean_norm_closed_ballE (a:NT) (r:R):
  metric_closed_ball a r=[set z:NT|N (z-a)<=r].
Proof.
apply:funext=>z; apply:propext.
change (N (a-z)<=r <->N (z-a)<=r).
by rewrite (real_seminorm_subtract hN.1 a z).
Qed.

(** Source for [euclidean_norm_closed_ball_measure]: the original
    epsilon^n normalization in the smoothing estimate of
    Federer 4.1.2, p. 347. The actual
    ball-volume coefficient and dimension zero are retained. *)
Lemma euclidean_norm_closed_ball_measure (a:NT) (r:R):
  0<r ->(@euclidean_lebesgue_measure R n) (metric_closed_ball a r)=
    ((@euclidean_closed_unit_volume R n)*r^+n)%:E.
Proof.
move=>hr.
have h:=@euclidean_closed_ball_measure R n (a:IT) r hr.
change ((@euclidean_lebesgue_measure R n) (metric_closed_ball a r)=
  ((@euclidean_closed_unit_volume R n)*r^+n)%:E) in h.
exact h.
Qed.

(** Source for [euclidean_norm_closed_ball_compact]: the compact
    source ball used by the original local
    integrability hypothesis, Federer 4.1.2, p. 347. *)
Lemma euclidean_norm_closed_ball_compact (a:NT) (r:R):compact (metric_closed_ball a r).
Proof.
rewrite euclidean_norm_closed_ballE.
exact:(@finite_norm_closed_ball_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN a r).
Qed.
End EuclideanNormClosedBalls.
