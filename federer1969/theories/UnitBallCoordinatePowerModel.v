(** Federer 2.10.27, p. 191: an existence witness for the already
    specified coordinate-power integrand. Its values, not a new
    integrability axiom, determine the function. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  RealPower UnitBallCoordinatePowerSummability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [unit_ball_coordinate_power_model]: supporting
    witness in the real profile computation of Federer 2.10.27,
    p. 191. Set the coordinate power on the closed unit ball
    and zero outside, using the existing power at zero. *)
Definition unit_ball_coordinate_power_model (R:realType) n (i:'I_n) (q:R)
    (x:inner_metric_space (@euclidean_inner_productP R n)):R:=
  if inner_norm (@euclidean_inner_productP R n) x<= 1 then real_power `|x i| q else 0.

(** Source for [unit_ball_coordinate_power_model_laws]: the witness
    satisfies the independently stated value laws for the supporting
    integrand of Federer 2.10.27, p. 191. *)
Lemma unit_ball_coordinate_power_model_laws (R:realType) n (i:'I_n) (q:R):
  is_unit_ball_coordinate_power i q (unit_ball_coordinate_power_model i q).
Proof.
split=> x hx;rewrite /unit_ball_coordinate_power_model.
- by rewrite hx.
- by rewrite leNgt hx.
Qed.
