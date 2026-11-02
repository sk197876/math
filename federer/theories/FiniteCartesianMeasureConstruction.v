(** Existence witness for the inductive finite Cartesian products in Federer
    (1969), 2.6.5, p. 119 The construction uses the already sealed binary
    product and is hidden behind the finite-family interface. Countability
    is needed for arbitrary reassociation, not for existence with this fixed
    association. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP ProductMeasure FiniteCartesianMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section Construction.
Variable R : realType.
Variable X : nat -> choiceType.
Variable alpha : forall j, set (X j) -> \bar R.
Hypothesis h_alpha : forall j, is_measure (@alpha j).

(** Source for [finite_cartesian_measure_witness]: private recursive
    existence proof for the induction in Federer 2.6.5, p. 119 (. Each stage
    carries its proved measure laws. *)
Fixpoint finite_cartesian_measure_witness n :
    {mu : set (finite_cartesian_carrier X n) -> \bar R | is_measure mu} :=
  match n as k return {mu : set (finite_cartesian_carrier X k) -> \bar R | is_measure mu} with
  | 0 => exist _ (@alpha 0%N) (h_alpha 0%N)
  | k.+1 => exist _
      (product_measure (proj2_sig (finite_cartesian_measure_witness k)) (h_alpha k.+1))
      (product_measure_is_measure (proj2_sig (finite_cartesian_measure_witness k)) (h_alpha k.+1))
  end.

(** Source for [finite_cartesian_measure_family_exists]: existence
    of the abstract finite-product family of Federer 2.6.5,
    p. 119, for its fixed left association. The actual
    recursive witness remains within this construction module. *)
Theorem finite_cartesian_measure_family_exists :
  exists nu : forall n, set (finite_cartesian_carrier X n) -> \bar R,
    is_finite_cartesian_measure_family alpha nu.
Proof.
exists (fun n => proj1_sig (finite_cartesian_measure_witness n)); constructor.
- by [].
- move=> n; exact: product_measure_specification.
Qed.
End Construction.
