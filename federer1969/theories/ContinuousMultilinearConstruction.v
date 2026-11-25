(** Private existence witness for the multilinear-map space
    of Federer (1969), 3.1.11, p. 219. Bounded
    multilinear functions form a linear subspace. Its scalar
    supremum norm is hidden by the sealing module. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier RealNormUP
  ContinuousMultilinearUP BoundedMultilinearAlgebra MultilinearNormConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Witness.
Variable R : realType.
Variable k : nat.
Variables X Y : lmodType R.
Variable NX : X->R.
Variable NY : Y->R.
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Local Notation F := (GRing.Lmodule.clone R ({ffun 'I_k->X}->Y) _).

(** Source for [continuous_multilinear_subspace]: closure of
    the space asserted in Federer 3.1.11, p. 219.
    This is a private existence witness, not the public definition. *)
Definition continuous_multilinear_subspace : subspace F :=
  @Subspace R F (norm_bounded_multilinear NX NY)
    (@norm_bounded_multilinear_zero R k X Y NX NY hNY)
    (@norm_bounded_multilinear_add R k X Y NX NY hNY)
    (fun c f=>@norm_bounded_multilinear_scale R k X Y NX NY hNY c f).

(** Source for [continuous_multilinear_carrier]: private
    carrier witnessing the continuous multilinear-map space
    in Federer 3.1.11, p. 219. *)
Definition continuous_multilinear_carrier : lmodType R :=
  [the lmodType R of subspace_space continuous_multilinear_subspace].

(** Source for [continuous_multilinear_evaluation_linear]: linearity
    of point evaluation in the witness for Federer 3.1.11, p. 219. *)
Lemma continuous_multilinear_evaluation_linear (u : {ffun 'I_k->X}) :
  linear (fun z : continuous_multilinear_carrier=>subspace_val z u).
Proof.
move=> c z w.
exact: (congr1 (fun f : F=>f u)
  (@subspace_val_linear R F continuous_multilinear_subspace c z w)).
Qed.

(** Source for [continuous_multilinear_evaluation_witness]:
    linear point evaluation of the private witness for the
    space in Federer 3.1.11, p. 219. *)
Definition continuous_multilinear_evaluation_witness (u : {ffun 'I_k->X}) :
    Hom continuous_multilinear_carrier Y :=
  @HomMap R continuous_multilinear_carrier Y
    (fun z=>subspace_val z u)
    (introT (asboolP _) (continuous_multilinear_evaluation_linear u)).

(** Source for [continuous_multilinear_norm_witness]: private
    finite supremum witness for the norm in Federer 3.1.11,
    p. 219, with the correction of erratum p. 4,
    book p. 219 line 4. *)
Definition continuous_multilinear_norm_witness (z : continuous_multilinear_carrier) : R :=
  sval (constructive_indefinite_description
    (@multilinear_operator_norm_exists R k X Y NX NY hNX hNY
      (subspace_val z) (subspace_valP z))).

(** Source for [continuous_multilinear_witness_laws]: all
    defining promises of the continuous multilinear-map space
    in Federer 3.1.11, p. 219, are proved by the witness. *)
Theorem continuous_multilinear_witness_laws :
  is_continuous_multilinear_space NX NY
    continuous_multilinear_evaluation_witness continuous_multilinear_norm_witness.
Proof.
constructor.
- move=> z w he; apply: subspace_val_injective; apply: funext=> u.
  have hh := he u.
  exact hh.
- move=> z; exact: (subspace_valP z).1.
- move=> f hf; exists (@subspace_lift R F continuous_multilinear_subspace f hf).
  by move=> u.
- move=> z; exact: (svalP (constructive_indefinite_description
    (@multilinear_operator_norm_exists R k X Y NX NY hNX hNY
      (subspace_val z) (subspace_valP z)))).
Qed.
End Witness.
