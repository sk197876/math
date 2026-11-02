(** Private existence proof for the repeated use of 2.8.10 in Federer
    (1969), 2.8.12, p. 149. A state is a subset of Q with its inclusion
    proof; each next state removes a selected family. Only the abstract
    iteration laws are exposed downstream. Source context and indexing:
    RadiusSelectionIterationUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RadiusCoverSelectionUP RadiusCoverSelection
  RadiusSelectionIterationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Construction.
Variable R : realType.
Variable X : metricType R.
Variables tau mu : R.
Variable Q : set (X*R).
Hypothesis ht : 1 < tau.
Hypothesis hm : 0 < mu.
Hypothesis hQ : is_bounded_positive_radius_family mu Q.

(** Source for [radius_iteration_state_bounds]: the radius
    bound remains valid on each subset of Q used in Federer
    2.8.12, p. 149. Private supporting restriction law. *)
Lemma radius_iteration_state_bounds (s : {F : set (X*R) | F `<=` Q}) :
  is_bounded_positive_radius_family mu (sval s).
Proof. move=> p hp; exact: hQ p (svalP s p hp). Qed.

(** Source for [radius_iteration_state_selection]: apply 2.8.10
    to the current eligible subset in Federer 2.8.12, p. 149.
    The selected family is obtained from the existing sealed interface. *)
Definition radius_iteration_state_selection (s : {F : set (X*R) | F `<=` Q}) :=
  @radius_cover_selection R X tau mu (sval s) ht hm (@radius_iteration_state_bounds s).

(** Source for [radius_iteration_state_selection_laws]: conditions
    (1) and (2) for the current stage in Federer 2.8.12, p. 149.
    Private consequence of the preceding selection specification. *)
Lemma radius_iteration_state_selection_laws (s : {F : set (X*R) | F `<=` Q}) :
  is_radius_cover_selection tau (sval s) (radius_iteration_state_selection s).
Proof. exact: radius_cover_selection_specification. Qed.

(** Source for [radius_iteration_next_state]: removing the current
    selection, Federer 2.8.12, p. 149. Inclusion in Q is
    proved and carried by the private state. *)
Definition radius_iteration_next_state (s : {F : set (X*R) | F `<=` Q}) :
    {F : set (X*R) | F `<=` Q} :=
  exist (fun F => F `<=` Q) (sval s `\` radius_iteration_state_selection s)
    (fun p hp => svalP s p hp.1).

(** Source for [radius_iteration_state]: recursive witness of the successive
    remainders in Federer 2.8.12, p. 149. *)
Fixpoint radius_iteration_state n : {F : set (X*R) | F `<=` Q} :=
  if n is k.+1 then radius_iteration_next_state (radius_iteration_state k)
  else exist (fun F => F `<=` Q) Q (fun p hp => hp).

(** Source for [radius_selection_iteration_exists]: existence
    of the iteration in Federer 2.8.12, p. 149, by repeated
    use of the already proved parameter-selection lemma. This
    witness theorem is hidden behind the iteration seal. *)
Theorem radius_selection_iteration_exists :
  exists u : (nat -> set (X*R)) * (nat -> set (X*R)),
    is_radius_selection_iteration tau Q u.1 u.2.
Proof.
exists ((fun n => sval (radius_iteration_state n)),
  (fun n => radius_iteration_state_selection (radius_iteration_state n))); constructor.
- by [].
- move=> n; exact: radius_iteration_state_selection_laws.
- by move=> n.
Qed.
End Construction.
