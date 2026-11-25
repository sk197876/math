(** Federer (1969), 2.10.45, printed p. 202: rewrite the equivalent interval
    for c in precisely the printed normalisation c alpha(k)/alpha(k+m). The
    half-integral power is represented by sqrt(m+1)^(k+m) in the
    natural-degree theorem. Source context: SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import EuclideanBallVolume EuclideanProductCoefficient EuclideanProductCoefficientBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_product_coefficient_normalisation]: direct
    algebraic form of the displayed two-sided bound
    in 2.10.45, p. 202. Both endpoint identities
    use the actual positive unit-ball volumes; no
    numerical inequalities are introduced as assumptions. *)
Theorem euclidean_product_coefficient_normalisation (R : realType) m k (c : R) :
  euclidean_product_lower_coefficient R m k<=c ->
  c<=euclidean_product_upper_coefficient R m k ->
  (euclidean_unit_ball_volume R m)^-1<=
      c*euclidean_unit_ball_volume R k/euclidean_unit_ball_volume R (k+m) /\
  c*euclidean_unit_ball_volume R k/euclidean_unit_ball_volume R (k+m)<=
      (Num.sqrt m.+1%:R)^+(k+m)/(2:R)^+m.
Proof.
move=> hl hu.
pose D := euclidean_unit_ball_volume R k/euclidean_unit_ball_volume R (k+m).
have hD : 0<D := divr_gt0 (euclidean_unit_ball_volumeE R k).2 (euclidean_unit_ball_volumeE R (k+m)).2.
have hc : c*euclidean_unit_ball_volume R k/euclidean_unit_ball_volume R (k+m)=c*D.
  by rewrite /D mulrA.
have hlow : euclidean_product_lower_coefficient R m k*D=(euclidean_unit_ball_volume R m)^-1.
  rewrite /euclidean_product_lower_coefficient /D.
  field; rewrite ?gt_eqF //; exact: (euclidean_unit_ball_volumeE R _).2.
have hupp : euclidean_product_upper_coefficient R m k*D=(Num.sqrt m.+1%:R)^+(k+m)/(2:R)^+m.
  rewrite euclidean_product_coefficient_printed /D.
  field; rewrite ?expf_neq0 ?pnatr_eq0 ?gt_eqF //; exact: (euclidean_unit_ball_volumeE R _).2.
rewrite hc; split.
- have hh := ler_wpM2r (ltW hD) hl; by rewrite hlow in hh.
- have hh := ler_wpM2r (ltW hD) hu; by rewrite hupp in hh.
Qed.
