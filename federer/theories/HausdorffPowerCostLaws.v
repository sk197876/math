(** Supporting numerical laws for the normalized diameter gauge in Federer
    (1969), 2.10.2, p. 171. These are integer-degree specializations *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import HausdorffDiameterCost ExtendedSupremumPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [hausdorff_power_cost_finite]: supporting
    finite-real evaluation of the gauge in Federer
    2.10.2, p. 171, retaining the degree-zero convention. *)
Lemma hausdorff_power_cost_finite (R : realType) (m : nat) (d : R) :
  hausdorff_power_cost m d%:E=(hausdorff_normalisation R m*d^+m)%:E.
Proof. by rewrite /hausdorff_power_cost -EFin_expe -EFinM. Qed.

(** Source for [hausdorff_power_cost_monotone]: supporting
    monotonicity on nonnegative extended diameters for the
    covering comparisons in Federer 2.10.2, p. 171. *)
Lemma hausdorff_power_cost_monotone (R : realType) (m : nat) (d e : \bar R) :
  (0<=d)%E -> (d<=e)%E -> (hausdorff_power_cost m d<=hausdorff_power_cost m e)%E.
Proof.
move=> hd hde; rewrite /hausdorff_power_cost.
apply: lee_wpmul2l; first by rewrite lee_fin; exact: ltW (@hausdorff_normalisation_positive R m).
exact: nonnegative_extended_power_monotone hd hde.
Qed.
