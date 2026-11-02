(** Numerical conclusion from the compact class in Federer (1969), 2.10.32,
    p. 197. Apply 2.10.31 to its proved closedness and Steiner stability. A
    centred ball has equal volume and exterior-diameter cost, so lambda is
    at most mu. Retain the origin alternative as the radius-zero closed ball
    and use the same identity; this treats dimension zero uniformly and does
    not need a positive lambda for this supporting comparison. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric CompactSetDistanceProfile CompactHausdorffMetric
  MetricClosedBalls EuclideanLebesgueDimensions ExteriorMeasureGauge EuclideanBallExteriorCost
  SteinerFamilyBallTheorem SteinerVolumeCostFamilyUP SteinerVolumeCostFamilyClosed SteinerVolumeCostFamilyStable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_volume_cost_threshold_comparison]: direct
    conclusion lambda<=mu from nonempty C in
    2.10.32, p. 197. The printed positive
    thresholds are included. Keeping the zero-ball
    alternative also permits arbitrary lambda and
    nonnegative mu in this intermediate result. *)
Theorem steiner_volume_cost_threshold_comparison (R : realType) (n : nat) (lambda mu : R) :
  0<=mu -> @steiner_volume_cost_family R n lambda mu !=set0 -> lambda<=mu.
Proof.
move=> hmu hne.
have [S [hS hshape]] := @federer_2_10_31 R n (@steiner_volume_cost_family R n lambda mu) hne
  (@steiner_volume_cost_family_closed R n lambda mu hmu)
  (@steiner_volume_cost_family_stable R n lambda mu).
have [_ [hvol hcost]] := hS.
have heval : exterior_diameter_cost n (val S)=euclidean_lebesgue_measure n (val S).
  case: hshape=> [hsingle|[r [hr hball]]].
  - pose E := inner_metric_space (@euclidean_inner_productP R n).
    have hz : metric_closed_ball (0 : E) 0=[set (0 : E)].
      apply/seteqP; split=> x hx.
      + have hzero : mdist (0 : E) x=0.
          apply/eqP; rewrite eq_le mdist_ge0 andbT; exact hx.
        exact (esym (@mdist_positivity R E 0 x hzero)).
      + by rewrite hx /metric_closed_ball /= mdistxx.
    rewrite hsingle -hz; exact (@euclidean_closed_ball_exterior_volume R n 0 (lexx 0)).
  - rewrite hball; exact (@euclidean_closed_ball_exterior_volume R n r (ltW hr)).
rewrite -heval in hvol.
have hh := le_trans hvol hcost; by move: hh; rewrite lee_fin.
Qed.
