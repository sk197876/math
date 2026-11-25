(** Federer (1969), 2.2.15, p. 71: continuous approximants to the
    characteristic function of a nonempty closed set, built from distance to
    that set. We use the explicit proof variant max(0,1-n*d) in place of the
    printed 2^(-n*d). Both equal one on the set and converge pointwise to
    zero outside it. The cutoff variant avoids introducing a separate
    real-exponential construction; the distance and smallest-class argument
    are unchanged. Scalar continuity uses pseudometric_normed_Zmodule and
    normed_module. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground MetricSetDistanceUP
  MetricSetDistanceBasic MetricSetDistanceContinuity PointwiseLimit
  PointwiseEventuallyConstant CharacteristicFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_distance_cutoff]: supporting construction
    for Federer 2.2.15, p. 71. This is the documented
    piecewise-linear replacement for the printed exponential approximant. *)
Definition closed_distance_cutoff (R : realType) (X : Type) (d : X -> R) n
    (x : X) : real_line_metric R := Order.max 0 (1 - n%:R * d x).

(** Source for [closed_distance_cutoff_continuous]: supporting
    continuity of the distance-based approximants in Federer 2.2.15,
    p. 71. Scalar multiplication, subtraction and maximum preserve
    continuity; only the abstract distance laws are used. *)
Lemma closed_distance_cutoff_continuous (R : realType) (X : metricType R)
    (A : set X) (d : X -> R) (hd : is_metric_set_distance A d) n :
  continuous (closed_distance_cutoff d n).
Proof.
rewrite /closed_distance_cutoff; move=> x; apply: (@continuous_max R X (fun _ => 0) (fun y => 1 - n%:R * d y) x); first exact: cvg_cst.
apply: cvgB; first exact: cvg_cst.
apply: cvgM; first exact: cvg_cst.
exact: (@metric_set_distance_continuous R X A d hd x).
Qed.

(** Source for [closed_distance_cutoff_zero_distance]: supporting
    on-set value in the characteristic-function approximation of
    Federer 2.2.15, p. 71. The cutoff is exactly
    one wherever the distance is zero, including stage zero. *)
Lemma closed_distance_cutoff_zero_distance (R : realType) (X : Type)
    (d : X -> R) x n : d x = 0 -> closed_distance_cutoff d n x = 1.
Proof. move=> hd; by rewrite /closed_distance_cutoff hd mulr0 subr0 max_r // ler01. Qed.

(** Source for [closed_distance_cutoff_eventually_zero]: supporting
    off-set convergence in Federer 2.2.15, p. 71,
    for the documented cutoff variant. Positive distance makes
    n*d at least one at all sufficiently large natural stages. *)
Lemma closed_distance_cutoff_eventually_zero (R : realType) (X : Type)
    (d : X -> R) x : 0 < d x -> exists N, forall n,
  (N <= n)%N -> closed_distance_cutoff d n x = 0.
Proof.
move=> hd; pose N := Num.bound (d x)^-1.
have hN : (d x)^-1 < N%:R by apply: archi_boundP; rewrite invr_ge0; exact: ltW hd.
exists N=> n hn.
have hnn : (N%:R : R) <= n%:R by rewrite ler_nat.
have hh : (d x)^-1 < n%:R := lt_le_trans hN hnn.
have h1 : 1 < n%:R * d x by rewrite -ltr_pdivrMr // div1r.
rewrite /closed_distance_cutoff max_l // subr_le0; exact: ltW h1.
Qed.
