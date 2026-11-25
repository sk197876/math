(** Federer (1969), 3.4.8(2), p. 326:
    the original finite minimum behind its independent
    opaque attainment and minimality laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import AnalyticReductionDepthUP AnalyticReductionDepthExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type AnalyticReductionDepthSignature.
(** Source for [value]: depth as the least nonempty
    directional intersection, 3.4.8(2), p. 326. *)
Parameter value:forall n (O:Type) (g0:O) (B:'I_n->set O),nat.
(** Source for [laws]: the exact original finite-minimum
    specification, 3.4.8(2), p. 326. *)
Parameter laws:forall n (O:Type) (g0:O) (B:'I_n->set O),
  is_analytic_reduction_depth B (@value n O g0 B).
End AnalyticReductionDepthSignature.
Module AnalyticReductionDepth:AnalyticReductionDepthSignature.
(** Source for [value]: private selection from proved
    existence, 3.4.8(2), p. 326. *)
Definition value n (O:Type) (g0:O) (B:'I_n->set O):=
  projT1 (cid (@analytic_reduction_depth_exists n O g0 B)).
(** Source for [laws]: the private minimum satisfies
    the original independent laws, 3.4.8(2), p. 326. *)
Lemma laws n (O:Type) (g0:O) (B:'I_n->set O):
  is_analytic_reduction_depth B (@value n O g0 B).
Proof. exact:(projT2 (cid (@analytic_reduction_depth_exists n O g0 B))). Qed.
End AnalyticReductionDepth.
