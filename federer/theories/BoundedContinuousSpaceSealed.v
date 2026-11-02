(** Opaque realisation of the space E of all bounded real valued continuous
    functions on a metric space Y, with the norm nu(f) = sup im |f|, Federer
    (1969), 2.5.16, p. 110. Only the vector space, the evaluation, the norm
    and their abstract laws are exposed. Source context:
    BoundedContinuousSpaceUP.v. *)
From mathcomp Require Import all_boot all_algebra reals topology.
From Federer Require Import BoundedContinuousSpaceUP BoundedContinuousSpaceConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type BoundedContinuousSpaceSignature.
(** Source for [space]: the vector space E of Federer 2.5.16, p. 110. *)
Parameter space : forall (R : realType) (Y : metricType R), lmodType R.
(** Source for [value]: evaluation of the members of E, Federer 2.5.16, p. 110. *)
Parameter value : forall (R : realType) (Y : metricType R), @space R Y -> Y -> R.
(** Source for [norm]: the norm nu(f) = sup im |f| of Federer 2.5.16, p. 110. *)
Parameter norm : forall (R : realType) (Y : metricType R), @space R Y -> R.
(** Source for [laws]: the abstract laws of E and nu, Federer 2.5.16, p. 110. *)
Parameter laws : forall (R : realType) (Y : metricType R),
  is_bounded_continuous_space (@value R Y) (@norm R Y).
End BoundedContinuousSpaceSignature.

Module BoundedContinuousSpace : BoundedContinuousSpaceSignature.
(** Source for [space]: private witness for E, Federer 2.5.16, p. 110. *)
Definition space (R : realType) (Y : metricType R) := [the lmodType R of BoundedContinuousFunction Y].
(** Source for [value]: private evaluation witness, Federer 2.5.16, p. 110. *)
Definition value (R : realType) (Y : metricType R) : @space R Y -> Y -> R :=
  @bounded_continuous_value R Y.
(** Source for [norm]: private norm witness, Federer 2.5.16, p. 110. *)
Definition norm (R : realType) (Y : metricType R) : @space R Y -> R :=
  @bounded_continuous_norm R Y.
(** Source for [laws]: the witnesses satisfy the abstract laws,
    Federer 2.5.16, p. 110. *)
Lemma laws (R : realType) (Y : metricType R) : is_bounded_continuous_space (@value R Y) (@norm R Y).
Proof. exact: bounded_continuous_space_witness. Qed.
End BoundedContinuousSpace.
