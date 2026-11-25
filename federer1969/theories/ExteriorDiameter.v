(** Public exterior-product diameter for Federer (1969), 2.10.3, p. 171. The
    selected supremum is accessed through its abstract laws; the existence
    witness is hidden. Source context and conventions: ExteriorDiameterUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations ExteriorDiameterUP ExteriorDiameterLaws ExteriorDiameterSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [extended_exterior_diameter]: public supremum
    in the cost formula of Federer 2.10.3, p. 171. *)
Definition extended_exterior_diameter (R : realType) (n m : nat) (A : set (R_n R n)) :=
  @ExteriorDiameter.value R n m A.

(** Source for [extended_exterior_diameter_specification]:
    public least-upper-bound laws for Federer 2.10.3, p. 171. *)
Lemma extended_exterior_diameter_specification (R : realType) (n m : nat) (A : set (R_n R n)) :
  is_exterior_diameter m A (extended_exterior_diameter m A).
Proof. exact: ExteriorDiameter.laws. Qed.

(** Source for [extended_exterior_diameter_mono]: supporting
    monotonicity of the gauge in Federer 2.10.3,
    p. 171, using the public supremum laws. *)
Lemma extended_exterior_diameter_mono (R : realType) (n m : nat) (A B : set (R_n R n)) :
  A `<=` B -> (extended_exterior_diameter m A<=extended_exterior_diameter m B)%E.
Proof. exact: exterior_diameter_inclusion_bound
  (extended_exterior_diameter_specification m A) (extended_exterior_diameter_specification m B). Qed.
