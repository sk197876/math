(** Private graph witness for Federer (1969), 3.2.20, p. 256.
    The relation is already single valued by the proved uniqueness laws.
    Only the sealing module and assumptions audit may import this module. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations PartialFunctionUP
  MeasureApproximateJacobianUP MeasureApproximateJacobianLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [measure_approximate_jacobian_graph_exists]: supporting
    existence of the exact partial approximate Jacobian in Federer
    3.2.20, p. 256. Use the specified value relation and
    its proved uniqueness; no out-of-domain value is supplied. The
    graph implementation is hidden by opaque module ascription. *)
Theorem measure_approximate_jacobian_graph_exists (R : realType) n k
    (phi : set (R_n R n) -> \bar R) m q
    (f : partial_function (R_n R n) (R_n R k)) :
  exists J : partial_function (R_n R n) R,
    is_measure_approximate_jacobian_graph phi m q f J.
Proof.
exists (@Build_partial_function (R_n R n) R
  (fun a j=>has_measure_approximate_jacobian phi m q f a j)
  (fun a j l hj hl=>measure_approximate_jacobian_unique hj hl)).
by move=> a j.
Qed.
