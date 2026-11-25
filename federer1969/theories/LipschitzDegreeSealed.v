(** Federer (1969), 4.1.26, p. 383:
    the original signed degree has an
    independently specified opaque partial value.
    Its numerical-sum witness and any extensions
    at undefined points stay hidden. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct PartialFunctionUP
  LipschitzDegreeUP LipschitzDegreeExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type LipschitzDegreeSignature.
(** Source for [value]: degree f restricted to A,
    the original signed density in 4.1.26, p. 383. *)
Parameter value:forall (R:realType) m (f:R_n R m->R_n R m)
  (A:set (R_n R m)),partial_function (R_n R m) R.
(** Source for [laws]: the independently specified signed
    fibre-sum graph of 4.1.26, p. 383. *)
Parameter laws:forall (R:realType) m f A,
  @is_lipschitz_degree R m f A (@value R m f A).
End LipschitzDegreeSignature.

Module LipschitzDegree:LipschitzDegreeSignature.
(** Source for [value]: select only the proved
    degree graph from 4.1.26, p. 383. *)
Definition value (R:realType) m (f:R_n R m->R_n R m) (A:set (R_n R m)):=
  projT1 (cid (@lipschitz_degree_exists R m f A)).
(** Source for [laws]: the hidden partial function
    has exactly the original graph, 4.1.26, p. 383. *)
Lemma laws (R:realType) m f A:
  @is_lipschitz_degree R m f A (@value R m f A).
Proof. exact:projT2 (cid (@lipschitz_degree_exists R m f A)). Qed.
End LipschitzDegree.

Arguments LipschitzDegree.value : clear implicits.
Arguments LipschitzDegree.laws : clear implicits.
