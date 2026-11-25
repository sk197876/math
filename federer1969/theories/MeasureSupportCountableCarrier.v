(** Federer (1969), 3.3.18, p. 301: an actual closed
    countable carrier gives countable topological support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import MeasureSupportUP MeasureSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_support_countable_closed_carrier]: supporting
    the countable-spt-phi assertion in Federer 3.3.18, p. 301.
    Each point outside the actual closed carrier has its open null
    complement as a neighbourhood, so the original sealed support
    lies inside the same countable carrier. No merely countable
    dense atomic carrier is mistaken for topological support. *)
Lemma measure_support_countable_closed_carrier (R:realType) (X:topologicalType)
    (mu:set X->\bar R) (E:set X):
  countable E ->closed E ->mu (~` E)= 0 ->countable (measure_support mu).
Proof.
move=>hCountable hClosed hOutside.
have hSub:measure_support mu `<=` E.
  move=>x hx; apply:contrapT=>hNot.
  have hSupport:=(measure_support_neighborhood_law (measure_support_specification mu) x).1 hx.
  exact:hSupport (~` E) (closed_openC hClosed) hNot hOutside.
exact:sub_countable (subset_card_le hSub) hCountable.
Qed.
