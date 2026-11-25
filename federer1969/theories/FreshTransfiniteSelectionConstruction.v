(** Private transfinite-choice construction for Federer (1969), 2.2.4, p. 62
    A fresh-point hypothesis at each stage gives a selection distinct from
    all its predecessors. The proof uses only logical well-founded
    recursion, with the predecessor relation proved well founded locally.
    The step hypothesis is discharged by cardinal bounds in the application;
    it is not introduced as a global axiom. Source context:
    SeparableMetricBaseConstruction.v. *)
From Corelib Require Import Init.Wf.
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import WellOrderRecursionBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [well_founded_fresh_selection_exists]: supporting transfinite
    recursion in Federer 2.2.4, p. 62. If each stage can choose a member of
    its prescribed set different from all previously chosen values,
    well-founded recursion supplies the whole selection with those laws. *)
Theorem well_founded_fresh_selection_exists (I T : Type) (r : I -> I -> Prop)
    (E : I -> set T) : well_founded r ->
  (forall i (f : forall j, r j i -> T),
    exists x, E i x /\ forall j (h : r j i), x <> f j h) ->
  exists f : I -> T, forall i, E i (f i) /\ forall j, r j i -> f i <> f j.
Proof.
move=> hw hex.
pose step i (f : forall j, r j i -> T) := projT1 (cid (hex i f)).
have hext i (f g : forall j, r j i -> T) :
    (forall j h, f j h = g j h) -> step i f = step i g.
  move=> h; have he : f = g by apply: functional_extensionality_dep=> j; apply: funext=> p; exact: h.
  by rewrite he.
pose f := @Fix I r hw (fun _ => T) step.
have hf i : f i = step i (fun j _ => f j).
  exact: (@Fix_eq I r hw (fun _ => T) step hext i).
exists f=> i; have hs := projT2 (cid (hex i (fun j _ => f j))).
change (E i (step i (fun j _ => f j)) /\
  forall j (h : r j i), step i (fun j _ => f j) <> f j) in hs.
rewrite (hf i); exact hs.
Qed.
