(** Supporting general topology for Federer (1969), 2.2.9, p. 65:
    homeomorphism with a subset equipped with its relative topology. We use
    the standard continuous-bijection-and-open-map characterization,
    expressing relative openness through ambient open sets. This avoids
    imposing an arbitrary topology on points outside the image. Source
    editions: NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_homeomorphism_onto]: supporting abstract homeomorphism
    specification for Federer 2.2.9, p. 65: g is injective with image G,
    continuous, and open into G's relative topology. No unproved global
    axioms are introduced. *)
Record is_homeomorphism_onto (S T : topologicalType) (G : set T) (g : S -> T) : Prop := {
  homeomorphism_onto_injective : injective g;
  homeomorphism_onto_image : g @` setT = G;
  homeomorphism_onto_continuous : continuous g;
  homeomorphism_onto_open : forall O : set S, open O ->
    exists V : set T, open V /\ g @` O = G `&` V
}.
