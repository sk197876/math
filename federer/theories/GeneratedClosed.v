(** Federer (1969), 2.2.1, p. 60: public interfaces for the two generated
    closure families. The parameter d selects disjoint-only unions when
    true, unrestricted unions when false. Source context:
    CountablyClosedFamilyUP.v. Only sealed laws are used. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import BorelFamilyUP GeneratedBorel CountablyClosedFamilyUP
  GeneratedClosedSealed BorelGenerationCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [generated_closed_family]: Federer 2.2.1,
    p. 60, the smallest family satisfying the selected countable
    closure conditions and containing S. *)
Definition generated_closed_family (d : bool) (I : choiceType)
    (X : set I) (S : set (set I)) (hS : forall A, S A -> A `<=` X) :=
  GeneratedClosed.value d hS.

(** Source for [generated_closed_family_specification]: Federer
    2.2.1, p. 60, the sealed family has the prescribed closure,
    containment and minimality laws. *)
Lemma generated_closed_family_specification (d : bool) (I : choiceType)
    (X : set I) (S : set (set I)) (hS : forall A, S A -> A `<=` X) :
  is_generated_closed_family d X S (generated_closed_family d hS).
Proof. exact: GeneratedClosed.laws. Qed.

(** Source for [generated_closed_family_is_closed]: Federer
    2.2.1, p. 60, closure of the generated family under the
    selected countable union law and nonempty countable intersections. *)
Lemma generated_closed_family_is_closed (d : bool) (I : choiceType)
    (X : set I) (S : set (set I)) (hS : forall A, S A -> A `<=` X) :
  is_countably_closed_family d X (generated_closed_family d hS).
Proof. exact: generated_closed_family_laws (generated_closed_family_specification d hS). Qed.

(** Source for [generated_closed_family_generator]: Federer
    2.2.1, p. 60, the generated closure family contains S. *)
Lemma generated_closed_family_generator (d : bool) (I : choiceType)
    (X : set I) (S : set (set I)) (hS : forall A, S A -> A `<=` X) :
  S `<=` generated_closed_family d hS.
Proof. exact: generated_closed_family_contains (generated_closed_family_specification d hS). Qed.

(** Source for [generated_closed_family_minimal]: Federer
    2.2.1, p. 60, minimality among families with the selected
    closure properties and containing S. *)
Lemma generated_closed_family_minimal (d : bool) (I : choiceType)
    (X : set I) (S : set (set I)) (hS : forall A, S A -> A `<=` X)
    (F : set (set I)) : is_countably_closed_family d X F -> S `<=` F ->
  generated_closed_family d hS `<=` F.
Proof. exact: (@generated_closed_family_least d I X S _ (generated_closed_family_specification d hS) F). Qed.

(** Source for [generated_closed_borel_eq]: Federer 2.2.1, p. 60, public
    equality in both generation criteria, using erratum p. 1, book p. 60
    line 4, empty set in S. *)
Theorem generated_closed_borel_eq (d : bool) (I : choiceType)
    (X : set I) (S : set (set I)) (hS : forall A, S A -> A `<=` X) :
  S set0 -> (forall A, S A -> generated_closed_family d hS (X `\` A)) ->
  generated_closed_family d hS = generated_borel_family hS.
Proof.
move=> h0 hc; apply: generated_borel_family_unique _ (generated_borel_family_specification hS).
exact: (@generated_closed_family_borel_criterion d I X S _
  (generated_closed_family_specification d hS) h0 hc).
Qed.
