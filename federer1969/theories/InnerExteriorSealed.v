(** Federer (1969), 1.7.5, p. 31: a sealed algebra extension of the
    polarity. Only the specification is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import InnerProductUP InnerExteriorUP InnerExteriorConstruction
  AlgebraUP ExteriorAlgebra AlternatingUnit ScalarCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type InnerExteriorSig.
(** Source for [map]: Federer 1.7.5, p. 31, gamma is
    the graded algebra extension of the polarity. *)
Parameter map : forall (R : realFieldType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R), is_inner_product B ->
    algebra_map (exterior_algebra V)
      (alternating_unital_algebra h2 V (scalar_algebra R)).
(** Source for [laws]: Federer 1.7.5, p. 31, gamma
    satisfies the abstract extension laws. *)
Parameter laws : forall (R : realFieldType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B),
    is_inner_exterior_extension hB (@map R h2 V B hB).
End InnerExteriorSig.
Module InnerExterior : InnerExteriorSig.
(** Source for [map]: Federer 1.7.5, p. 31, select
    the proved extension witness and hide its construction. *)
Definition map (R : realFieldType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B) :=
  sval (constructive_indefinite_description
    (@inner_exterior_extension_exists R h2 V B hB)).
(** Source for [laws]: Federer 1.7.5, p. 31, the
    selected extension satisfies its defining specification. *)
Lemma laws (R : realFieldType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B) :
  is_inner_exterior_extension hB (@map R h2 V B hB).
Proof. exact: (svalP (constructive_indefinite_description
  (@inner_exterior_extension_exists R h2 V B hB))). Qed.
End InnerExterior.
