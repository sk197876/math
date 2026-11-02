(** Federer (1969), 1.10.4, p. 46: degree is the supremum of the nonzero
    coefficient degrees together with {0}. Supporting abstraction for any
    nonnegatively graded vector space. The specification here follows
    Federer. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded GradedSums.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

From Federer Require Import GradedDegreeUP GradedDegreeConstruction.
Module Type GRADED_DEGREE.
(** Source for [degree]: Federer 1.10.4, p. 46, abstract finite
    degree operation, specified by its supremum laws below. *)
Parameter degree : forall (K : fieldType) (V : lmodType K), grading V -> V -> nat.
(** Source for [laws]: Federer 1.10.4, p. 46, required specification
    of the degree operation. The implementation proves these laws. *)
Parameter laws : forall (K : fieldType) (V : lmodType K) (G : grading V) x,
  is_graded_degree G x (@degree K V G x).
End GRADED_DEGREE.
Module GradedDegree : GRADED_DEGREE.
(** Source for [degree]: Federer 1.10.4, p. 46, the private finite
    maximum supplies existence of the abstract operation. *)
Definition degree := @graded_degree_witness.
(** Source for [laws]: Federer 1.10.4, p. 46, the proved witness
    satisfies the signature; opaque ascription hides its construction. *)
Definition laws := @graded_degree_witness_laws.
End GradedDegree.
