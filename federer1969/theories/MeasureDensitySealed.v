(** Opaque density-measure interface for Federer (1969), 2.4.10, p. 85. Only
    the defining upper-integral law is exposed; the public measure and
    integration results depend on that law. Source context:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureDensityUP MeasureDensityConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type MeasureDensitySignature.
(** Source for [value]: the density set function of
    Federer 2.4.10, p. 85. *)
Parameter value : forall (R : realType) (X : choiceType),
  (set X -> \bar R) -> partial_function X (extended_real_line R) -> set X -> \bar R.
(** Source for [laws]: the upper-integral formula prescribing
    the density set function in Federer 2.4.10, p. 85. *)
Parameter laws : forall (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (h : partial_function X (extended_real_line R)), is_measure_density mu h (@value R X mu h).
End MeasureDensitySignature.
Module MeasureDensity : MeasureDensitySignature.
(** Source for [value]: private selection of the proved
    density witness for Federer 2.4.10, p. 85. *)
Definition value (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (h : partial_function X (extended_real_line R)) := projT1 (cid (measure_density_exists mu h)).
(** Source for [laws]: the selected witness satisfies the
    density formula of Federer 2.4.10, p. 85. *)
Lemma laws (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (h : partial_function X (extended_real_line R)) : is_measure_density mu h (@value R X mu h).
Proof. exact: projT2 (cid (measure_density_exists mu h)). Qed.
End MeasureDensity.
