(** Private existence witness for the density set function in Federer
    (1969), 2.4.10, p. 85. Its formula uses the existing sealed
    upper-integral interface; measure laws are derived separately from the
    abstract formula. Source context: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureSubsetIntegral MeasureDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measure_density_exists]: proved existence
    of the set function prescribed by Federer 2.4.10,
    p. 85, second display. *)
Lemma measure_density_exists (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (h : partial_function X (extended_real_line R)) :
  exists nu, is_measure_density mu h nu.
Proof. exists (fun A => measure_subset_upper_integral mu A h); by move=> A. Qed.
