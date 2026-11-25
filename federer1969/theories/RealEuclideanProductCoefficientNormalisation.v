(** Federer 2.10.45, p. 202: retain the exact printed interval
    1/alpha(m)<=c alpha(k)/alpha(k+m)<=(m+1)^((k+m)/2)/2^m
    for arbitrary real k>=0. The square-root power is the same positive
    real power. The natural Euclidean dimension m may be zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import RealHausdorffBallCoefficient RealHausdorffNormalisation
  RealPower RealPowerSuccessor RealPowerNaturalHausdorff EuclideanBallVolume
  RealEuclideanProductCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_euclidean_product_alpha_ratio]: supporting
    cancellation of powers of two in the coefficient display of
    Federer 2.10.45, p. 202. The numerator and denominator are the
    actual Gamma-defined alpha values. *)
Lemma real_euclidean_product_alpha_ratio (R : realType) m (k : R)
    (hk : 0 <= k) :
  real_hausdorff_ball_coefficient hk/
    real_hausdorff_ball_coefficient (addr_ge0 hk (ler0n R m)) =
  (real_hausdorff_normalisation hk/
    real_hausdorff_normalisation (addr_ge0 hk (ler0n R m)))/(2:R)^+m.
Proof.
have htwo : real_power (2:R) (k+m%:R) = real_power (2:R) k*(2:R)^+m.
  by rewrite real_power_add_exponents_positive ?ltr0n // real_power_natural_exponent ?ler0n.
rewrite -!real_hausdorff_ball_coefficient_cost htwo.
have hkpow : real_power (2:R) k != 0.
  apply: lt0r_neq0; apply: real_power_strictly_positive; by rewrite ltr0n.
have hnorm : real_hausdorff_normalisation (addr_ge0 hk (ler0n R m)) != 0.
  exact: lt0r_neq0 (real_hausdorff_normalisation_positive _).
have hm : (2:R)^+m != 0 by rewrite expf_neq0 // pnatr_eq0.
field; by rewrite hm hnorm hkpow.
Qed.

(** Source for [real_euclidean_product_coefficient_normalisation]:
    direct printed bounds in Federer 2.10.45, p. 202, in every
    nonnegative real section degree. Both endpoints follow from the
    proved product bounds; no numerical Gamma inequality is assumed. *)
Theorem real_euclidean_product_coefficient_normalisation (R : realType) m
    (k : R) (hk : 0 <= k) (c : R) :
  real_euclidean_product_lower_coefficient m hk <= c ->
  c <= real_euclidean_product_upper_coefficient m hk ->
  (euclidean_unit_ball_volume R m)^-1 <=
      c*real_hausdorff_ball_coefficient hk/
        real_hausdorff_ball_coefficient (addr_ge0 hk (ler0n R m)) /\
  c*real_hausdorff_ball_coefficient hk/
        real_hausdorff_ball_coefficient (addr_ge0 hk (ler0n R m)) <=
      real_power (Num.sqrt m.+1%:R) (k+m%:R)/(2:R)^+m.
Proof.
move=> hl hu.
pose D := real_hausdorff_ball_coefficient hk/
  real_hausdorff_ball_coefficient (addr_ge0 hk (ler0n R m)).
have hD : 0 < D.
  exact: divr_gt0 (real_hausdorff_ball_coefficient_positive hk)
    (real_hausdorff_ball_coefficient_positive _).
have hc : c*real_hausdorff_ball_coefficient hk/
    real_hausdorff_ball_coefficient (addr_ge0 hk (ler0n R m))=c*D.
  by rewrite /D mulrA.
have hlow : real_euclidean_product_lower_coefficient m hk*D =
    (euclidean_unit_ball_volume R m)^-1.
  have hm : real_hausdorff_ball_coefficient (ler0n R m)=euclidean_unit_ball_volume R m.
    exact: real_hausdorff_ball_coefficient_natural.
  rewrite /D real_euclidean_product_alpha_ratio -hm
    -real_hausdorff_ball_coefficient_cost /real_euclidean_product_lower_coefficient
    (@real_power_natural_exponent R (2:R) m (ler0n R 2)).
  field; rewrite ?expf_neq0 ?pnatr_eq0 ?gt_eqF //;
    exact: real_hausdorff_normalisation_positive.
have hupp : real_euclidean_product_upper_coefficient m hk*D =
    real_power (Num.sqrt m.+1%:R) (k+m%:R)/(2:R)^+m.
  rewrite /D real_euclidean_product_alpha_ratio /real_euclidean_product_upper_coefficient.
  field; rewrite ?expf_neq0 ?pnatr_eq0 ?gt_eqF //;
    exact: real_hausdorff_normalisation_positive.
rewrite hc; split.
- have hh := ler_wpM2r (ltW hD) hl; by rewrite hlow in hh.
- have hh := ler_wpM2r (ltW hD) hu; by rewrite hupp in hh.
Qed.
