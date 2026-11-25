(** Federer (1969), 4.1.26, p. 383: opaque
    access to the independently specified signed source
    summand. Only its exact partial graph is exposed;
    the differential and zero-extension existence witness
    remains hidden. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct PartialFunctionUP
  LipschitzDegreeSummandUP LipschitzDegreeSummandExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type LipschitzDegreeSummandSignature.
(** Source for [value]: the original signed determinant
    field on A in 4.1.26, p. 383. *)
Parameter value:forall (R:realType) m (f:R_n R m->R_n R m)
  (A:set (R_n R m)),partial_function (R_n R m) R.
(** Source for [laws]: the original pointwise partial-domain
    specification of 4.1.26, p. 383. *)
Parameter laws:forall (R:realType) m f A,
  @is_lipschitz_degree_summand R m f A (@value R m f A).
End LipschitzDegreeSummandSignature.

Module LipschitzDegreeSummand:LipschitzDegreeSummandSignature.
(** Source for [value]: choose only the independently
    proved original summand of 4.1.26, p. 383. *)
Definition value (R:realType) m (f:R_n R m->R_n R m) (A:set (R_n R m)):=
  projT1 (cid (@lipschitz_degree_summand_exists R m f A)).
(** Source for [laws]: the hidden witness satisfies
    exactly the original graph, 4.1.26, p. 383. *)
Lemma laws (R:realType) m f A:
  @is_lipschitz_degree_summand R m f A (@value R m f A).
Proof. exact:projT2 (cid (@lipschitz_degree_summand_exists R m f A)). Qed.
End LipschitzDegreeSummand.

Arguments LipschitzDegreeSummand.value : clear implicits.
Arguments LipschitzDegreeSummand.laws : clear implicits.
