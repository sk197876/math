(** Federer (1969), 2.10.3, p. 171: multiply the supremum of the
    exterior-product norms by alpha(m) 2^(-m). The degree m is a positive
    integer in the target item; the cost expression is also available at
    degree zero as supporting notation, without a claim about an additional
    printed measure. Source context: ExteriorDiameterUP.v. The normalization
    is the actual unit-ball volume of 2.7.16(1), p. 135, as in 2.10.2. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations HausdorffDiameterCost
  ExteriorDiameterUP ExteriorDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [exterior_diameter_cost]: direct normalized
    cost in Federer 2.10.3, p. 171. The supremum
    already has degree m in the endpoints, so no
    additional m-th power is applied to it. *)
Definition exterior_diameter_cost (R : realType) (n m : nat) (A : set (R_n R n)) : \bar R :=
  ((hausdorff_normalisation R m)%:E*extended_exterior_diameter m A)%E.

(** Source for [exterior_diameter_cost_nonnegative]: supporting
    nonnegative cost hypothesis for Caratheodory's construction
    in Federer 2.10.3, p. 171. *)
Lemma exterior_diameter_cost_nonnegative (R : realType) (n m : nat) (A : set (R_n R n)) :
  (0<=exterior_diameter_cost m A)%E.
Proof.
rewrite /exterior_diameter_cost; apply: mule_ge0.
- rewrite lee_fin; exact: ltW (@hausdorff_normalisation_positive R m).
- exact: exterior_diameter_nonnegative (extended_exterior_diameter_specification m A).
Qed.

(** Source for [exterior_diameter_cost_mono]: supporting
    monotonicity of the endpoint supremum in Federer
    2.10.3, p. 171, used to compare covering families. *)
Lemma exterior_diameter_cost_mono (R : realType) (n m : nat) (A B : set (R_n R n)) :
  A `<=` B -> (exterior_diameter_cost m A<=exterior_diameter_cost m B)%E.
Proof.
move=> hAB; rewrite /exterior_diameter_cost; apply: lee_wpmul2l.
- rewrite lee_fin; exact: ltW (@hausdorff_normalisation_positive R m).
- exact: extended_exterior_diameter_mono hAB.
Qed.
