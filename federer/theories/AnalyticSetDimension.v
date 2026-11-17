(** Federer (1969), 3.4.10, p. 337:
    global analytic-set dimension specified by the
    attained supremum of actual nonempty local dimensions.
    Reuse the opaque bounded-supremum interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness AnalyticSetLocalDepth
  BoundedNaturalSupremumUP BoundedNaturalSupremumSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_set_dimension]: the supremum
    in 3.4.10, p. 337. The selected
    value is opaque through BoundedNaturalSupremum; the
    empty-set value is explicitly an auxiliary totalization. *)
Definition analytic_set_dimension (R:realType) n (S:set (R_n R n)):nat:=
  @BoundedNaturalSupremum.value (R_n R n) S (@analytic_set_local_depth R n S) n
    (fun a _=>@analytic_set_local_depth_bound R n S a).

(** Source for [analytic_set_dimension_laws]: the original
    supremum laws of 3.4.10, p. 337,
    including attainment for nonempty analytic sets. *)
Theorem analytic_set_dimension_laws (R:realType) n (S:set (R_n R n)):
  is_bounded_natural_supremum S (@analytic_set_local_depth R n S)
    (@analytic_set_dimension R n S).
Proof.
exact:(@BoundedNaturalSupremum.laws (R_n R n) S (@analytic_set_local_depth R n S) n
  (fun a _=>@analytic_set_local_depth_bound R n S a)).
Qed.
