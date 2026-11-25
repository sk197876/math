(** Federer (1969), 2.2.15, p. 71: the sets whose characteristic functions
    are Baire form a Borel family containing the closed sets, hence all
    Borel sets. The proof uses the local family specification and its
    minimality laws. *)
From mathcomp Require Import all_boot classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground BorelFamilyUP BorelFamilyRedundancy
  TopologicalBorel CharacteristicFunctionUP CharacteristicFunctionSealed
  BaireFunctions BaireCharacteristicBasic BaireCharacteristicUnions ClosedCharacteristicBaire.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [baire_characteristic_borel_family]: direct
    family assertion for F in Federer 2.2.15, p. 71.
    Empty-set, complement and countable-union closure suffice for
    the local Borel-family specification. This part only requires
    a topological source; closed generators are added for metric sources. *)
Theorem baire_characteristic_borel_family (R : realType) (X : topologicalType) :
  is_borel_family setT (@has_baire_characteristic R X).
Proof.
apply: borel_family_of_union.
- exact: baire_characteristic_empty.
- by move=> A hA x hx.
- move=> A hA; rewrite setTD; exact: baire_characteristic_complement hA.
- move=> G hG hc; exact: baire_characteristic_countable_union hc hG.
Qed.

(** Source for [borel_set_has_baire_characteristic]: direct
    consequence that F contains every Borel subset in Federer
    2.2.15, p. 71. Closed sets have continuous
    approximants; complements supply the open generators. *)
Theorem borel_set_has_baire_characteristic (R : realType) (X : metricType R) (A : set X) :
  borel_set A -> has_baire_characteristic R A.
Proof.
apply: (@generated_borel_family_least X setT (@open X) _
  (borel_sets_specification X) (@has_baire_characteristic R X)).
- exact: baire_characteristic_borel_family.
- move=> U ho.
  have hc : has_baire_characteristic R (~` U).
    exists (@CharacteristicFunction.value R X (~` U)); split; first exact: CharacteristicFunction.laws.
    exact: closed_characteristic_baire (open_closedC ho) (@CharacteristicFunction.laws R X (~` U)).
  have hh := baire_characteristic_complement hc; by rewrite setCK in hh.
Qed.

(** Source for [borel_characteristic_baire]: public arbitrary-
    witness form of the characteristic-function result in Federer
    2.2.15, p. 71. The proof uses only the
    pointwise laws of the supplied characteristic function. *)
Theorem borel_characteristic_baire (R : realType) (X : metricType R) (A : set X)
    (f : X -> real_line_metric R) :
  borel_set A -> is_characteristic_function A f -> is_baire_function f.
Proof.
move=> hA hf; exact: baire_characteristic_transfer (borel_set_has_baire_characteristic hA) hf.
Qed.
