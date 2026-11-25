(** Opaque smooth unit cutoff from Federer
    (1969), 3.1.11, p. 223,
    for use in the partition of unity
    of 3.1.13, pp. 224–225. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import FlatExponentialSealed ScalarSmoothSequenceUP
  ScalarUnitCutoffUP ScalarUnitCutoffConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type ScalarUnitCutoffSignature.
(** Source for [value]: the second smooth
    scalar function in Federer 3.1.11, p. 223. *)
Parameter value : forall R : realType, R->R.
(** Source for [formula]: the exact printed
    formula in terms of the first flat
    function, Federer 3.1.11, p. 223. *)
Parameter formula : forall (R : realType) x, @value R x=
  FlatExponential.value (FlatExponential.value 1-FlatExponential.value x)/
    FlatExponential.value (FlatExponential.value (1:R)).
(** Source for [laws]: monotonicity, bounds
    and endpoint laws, Federer 3.1.11, p. 223. *)
Parameter laws : forall R : realType, is_scalar_unit_cutoff (@value R).
(** Source for [smooth_derivatives]: proved derivatives
    of every order, Federer 3.1.11, p. 223. *)
Parameter smooth_derivatives : forall R : realType,
  exists G : nat->R->R, is_scalar_smooth_derivative_sequence (@value R) G.
End ScalarUnitCutoffSignature.

Module ScalarUnitCutoff : ScalarUnitCutoffSignature.
(** Source for [value]: the proved witness
    of Federer's cutoff, 3.1.11, p. 223. *)
Definition value (R : realType) :=
  sval (constructive_indefinite_description (@scalar_unit_cutoff_exists R)).
(** Source for [formula]: the existence proof
    preserves the printed formula, Federer
    3.1.11, p. 223. *)
Lemma formula (R : realType) x : @value R x=
  FlatExponential.value (FlatExponential.value 1-FlatExponential.value x)/
    FlatExponential.value (FlatExponential.value (1:R)).
Proof. exact: (svalP (constructive_indefinite_description (@scalar_unit_cutoff_exists R))).1. Qed.
(** Source for [laws]: the cutoff laws
    are proved for the chosen witness,
    Federer 3.1.11, p. 223. *)
Lemma laws (R : realType) : is_scalar_unit_cutoff (@value R).
Proof. exact: (svalP (constructive_indefinite_description (@scalar_unit_cutoff_exists R))).2.1. Qed.
(** Source for [smooth_derivatives]: the witness
    has a proved derivative sequence,
    Federer 3.1.11, p. 223. *)
Lemma smooth_derivatives (R : realType) :
  exists G : nat->R->R, is_scalar_smooth_derivative_sequence (@value R) G.
Proof. exact: (svalP (constructive_indefinite_description (@scalar_unit_cutoff_exists R))).2.2. Qed.
End ScalarUnitCutoff.
