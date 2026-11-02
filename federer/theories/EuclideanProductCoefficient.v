(** Federer (1969), 2.10.45, printed pp. 202–203: the cube-cover coefficient
    xi equals alpha(k+m)/alpha(k) times 2^(-m) times (m+1)^((k+m)/2). In the
    current natural-degree interfaces write the half-power as
    sqrt(m+1)^(k+m). Derive its normalisation identities from the actual
    unit-ball volumes; no coefficient inequality is assumed. Source context:
    SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import EuclideanBallVolume HausdorffDiameterCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_product_upper_coefficient]: direct
    xi of 2.10.45, p. 202, expressed
    as the ratio of the existing diameter-cost
    normalisations times the product diameter factor. *)
Definition euclidean_product_upper_coefficient (R : realType) m k : R :=
  hausdorff_normalisation R (k+m)/hausdorff_normalisation R k*
    (Num.sqrt m.+1%:R)^+(k+m).

(** Source for [euclidean_product_upper_coefficient_positive]: supporting
    positivity of xi for the comparison and
    zero-mass case of 2.10.45, pp. 202–203.
    Either natural dimension may be zero. *)
Lemma euclidean_product_upper_coefficient_positive (R : realType) m k :
  0<euclidean_product_upper_coefficient R m k.
Proof.
rewrite /euclidean_product_upper_coefficient mulr_gt0 //.
- exact: divr_gt0 (hausdorff_normalisation_positive R (k+m)) (hausdorff_normalisation_positive R k).
- apply: exprn_gt0; by rewrite sqrtr_gt0 ltr0n.
Qed.

(** Source for [euclidean_product_coefficient_cost_identity]: supporting
    cancellation of the source k-dimensional cost
    coefficient in the final double sum of
    2.10.45, p. 203. *)
Lemma euclidean_product_coefficient_cost_identity (R : realType) m k :
  euclidean_product_upper_coefficient R m k*hausdorff_normalisation R k=
    hausdorff_normalisation R (k+m)*(Num.sqrt m.+1%:R)^+(k+m).
Proof.
rewrite /euclidean_product_upper_coefficient mulrAC divfK //.
exact: lt0r_neq0 (hausdorff_normalisation_positive R k).
Qed.

(** Source for [euclidean_product_coefficient_printed]: direct
    displayed expression for xi in 2.10.45,
    p. 202, with the half-power written
    as a natural power of the nonnegative square root. *)
Lemma euclidean_product_coefficient_printed (R : realType) m k :
  euclidean_product_upper_coefficient R m k=
    euclidean_unit_ball_volume R (k+m)/euclidean_unit_ball_volume R k*
      (Num.sqrt m.+1%:R)^+(k+m)/(2:R)^+m.
Proof.
rewrite /euclidean_product_upper_coefficient /hausdorff_normalisation exprD.
field; rewrite ?(gt_eqF (euclidean_unit_ball_volumeE R k).2) ?expf_neq0 ?pnatr_eq0 //.
Qed.

(** Source for [euclidean_product_coefficient_zero_first_dimension]: supporting
    m=0 boundary of xi in 2.10.45,
    pp. 202–203. The first factor consists
    of one point, and the coefficient is exactly one. *)
Lemma euclidean_product_coefficient_zero_first_dimension (R : realType) k :
  euclidean_product_upper_coefficient R 0 k= 1.
Proof.
rewrite /euclidean_product_upper_coefficient addn0 /= sqrtr1 expr1n mulr1 divff //.
exact: lt0r_neq0 (hausdorff_normalisation_positive R k).
Qed.
