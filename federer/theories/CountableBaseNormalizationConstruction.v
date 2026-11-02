(** Federer (1969), 2.2.11, p. 68: supporting normalization of an arbitrary
    enumerated open base, adjoining the empty set. The printed
    complement-of-union formula needs this member to represent the whole
    closed space. This is a local boundary clarification, not a listed
    erratum correction. Source context: CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import CountableOpenBaseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [normalized_countable_base_exists]: supporting
    existence for Federer 2.2.11, p. 68. Prepending the empty
    open set preserves every open-neighborhood refinement and
    supplies the harmless extra convention needed by the formula. *)
Lemma normalized_countable_base_exists (T : topologicalType) (U : nat -> set T) :
  (forall i, open (U i)) ->
  (forall V, open V -> forall x, V x -> exists i, U i x /\ U i `<=` V) ->
  exists W : nat -> set T, is_countable_open_base W.
Proof.
move=> ho hr; exists (fun i => if i is j.+1 then U j else set0).
constructor.
- by case=> [|i] /=; [exact: open0|exact: ho].
- by [].
- move=> V hV x hx; have [i hi] := hr V hV x hx; by exists i.+1.
Qed.
