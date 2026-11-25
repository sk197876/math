(** Private existence proof for the corrected topological construction
    supporting Federer (1969), 2.10.1, p. 170. Take the already sealed
    extended-real supremum of the already sealed refined-cover envelopes.
    The proof establishes the abstract specification; downstream proofs
    never unfold this construction. Source context and corrected convention:
    TopologicalCaratheodoryUP.v. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealBounds OpenRefiningEnvelopeUP OpenRefiningEnvelopeLaws
  OpenRefiningEnvelope TopologicalCaratheodoryUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [topological_caratheodory_exists]: proved
    existence of the abstract whole-space-open-cover supremum
    for the corrected topological extension of Federer 2.10.1,
    p. 170. This is a witness, not a new global axiom. *)
Theorem topological_caratheodory_exists (R : realType) (X : topologicalType)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R) :
  exists mu, is_topological_caratheodory S cost mu.
Proof.
pose phi := open_refining_envelope S cost.
pose V A := [set r : \bar R | exists H, is_whole_space_open_cover H /\ r=phi H A].
exists (fun A => extended_real_sup (V A)); constructor.
- move=> A H nu hH hn.
  have he := @open_refining_envelope_unique R X J S cost H nu (phi H)
    hn (open_refining_envelope_specification S cost H) A.
  rewrite he; apply: extended_real_sup_upper; by exists H.
- move=> A b hb; apply: extended_real_sup_least=> r [H [hH ->]].
  exact (hb H (phi H) hH (open_refining_envelope_specification S cost H)).
Qed.
