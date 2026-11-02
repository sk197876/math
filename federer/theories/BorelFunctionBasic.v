(** Federer (1969), 2.2.14, p. 70: inverse images of all Borel sets under
    Borel maps. The preimage family laws were proved for the 2.2.11
    transfer; we now apply them to the full Borel-function definition.
    Source context: BorelFunctionUP.v. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import BorelFamilyUP TopologicalBorel ContinuousBorelPreimages
  BorelFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_function_preimage]: direct consequence in Federer
    2.2.14, p. 70, first paragraph. The family of sets with Borel preimage
    is a Borel family containing the opens; minimality therefore includes
    every Borel set. *)
Theorem borel_function_preimage (X Y : topologicalType) (f : X -> Y) :
  is_borel_function f -> forall A, borel_set A -> borel_set (f @^-1` A).
Proof.
move=> hf; apply: (@generated_borel_family_least Y setT (@open Y) _
  (borel_sets_specification Y) [set A | borel_set (f @^-1` A)]).
- exact: borel_preimage_family_laws.
- exact hf.
Qed.

(** Source for [continuous_borel_function]: supporting case of Federer
    2.2.14, p. 70: continuous maps are Borel functions. *)
Lemma continuous_borel_function (X Y : topologicalType) (f : X -> Y) :
  continuous f -> is_borel_function f.
Proof.
move=> hf U hU; exact: (@continuous_borel_preimage X Y f hf U (open_borel_set hU)).
Qed.

(** Source for [identity_borel_function]: supporting identity case of the
    definition in Federer 2.2.14, p. 70 *)
Lemma identity_borel_function (X : topologicalType) : is_borel_function (@id X).
Proof. move=> U hU; exact: open_borel_set hU. Qed.

(** Source for [borel_function_composition]: supporting composition law for
    Federer 2.2.14, p. 70 The inner inverse image is Borel, so the all-Borel
    preimage theorem applies. *)
Lemma borel_function_composition (X Y Z : topologicalType) (f : X -> Y) (g : Y -> Z) :
  is_borel_function f -> is_borel_function g -> is_borel_function (g \o f).
Proof.
move=> hf hg U hU; change (borel_set (f @^-1` (g @^-1` U))).
exact: (@borel_function_preimage X Y f hf (g @^-1` U) (hg U hU)).
Qed.
