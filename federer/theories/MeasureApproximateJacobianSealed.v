(** Federer (1969), 3.2.20, p. 256: opaque approximate
    Jacobian graph. Only the exact specification is exposed; norm-cost
    and graph witnesses remain hidden. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations PartialFunctionUP
  MeasureApproximateJacobianUP MeasureApproximateJacobianConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type MEASURE_APPROXIMATE_JACOBIAN.
(** Source for [value]: the partial ap J_q f of Federer
    3.2.20, p. 256, with density dimension and exterior degree
    separated for 3.2.22, p. 258. Its implementation must prove
    the exact graph law below. *)
Parameter value : forall (R : realType) (n k : nat)
  (phi : set (R_n R n) -> \bar R) (m q : nat),
  partial_function (R_n R n) (R_n R k) -> partial_function (R_n R n) R.
(** Source for [laws]: the exact partial Jacobian graph in
    Federer 3.2.20, p. 256. This is an implementation obligation,
    discharged from the previously proved graph-existence theorem. *)
Parameter laws : forall (R : realType) n k (phi : set (R_n R n) -> \bar R) m q
  (f : partial_function (R_n R n) (R_n R k)),
  is_measure_approximate_jacobian_graph phi m q f (@value R n k phi m q f).
End MEASURE_APPROXIMATE_JACOBIAN.
Module MeasureApproximateJacobians : MEASURE_APPROXIMATE_JACOBIAN.
(** Source for [value]: select the proved partial graph supporting
    Federer 3.2.20, p. 256; opaque ascription hides this selection. *)
Definition value (R : realType) n k (phi : set (R_n R n) -> \bar R) m q
    (f : partial_function (R_n R n) (R_n R k)) :=
  projT1 (cid (@measure_approximate_jacobian_graph_exists R n k phi m q f)).
(** Source for [laws]: verify the selected graph's exact law
    for Federer 3.2.20, p. 256, from its proved existence. *)
Lemma laws (R : realType) n k (phi : set (R_n R n) -> \bar R) m q
    (f : partial_function (R_n R n) (R_n R k)) :
  is_measure_approximate_jacobian_graph phi m q f (@value R n k phi m q f).
Proof. exact: projT2 (cid (@measure_approximate_jacobian_graph_exists R n k phi m q f)). Qed.
End MeasureApproximateJacobians.
