(** Federer (1969), 2.2.5, pp. 62-63: a compact subset of the union of open
    null sets has a finite subcover. Federer's erratum p. 1, book p. 63 line
    2, corrects this to "finitely many open sets". This is an adapter for
    general-topology background, removing the library's inhabited-space
    restriction. Source context: RadonMeasureUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot finmap boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [pointed_cover_space]: supporting topology adapter
    for Federer 2.2.5, p. 63: a fresh type alias carries a chosen
    ambient point while preserving the original topology. It is used
    only to apply the general finite-cover theorem, not to change the
    definition of a Radon measure or assume an inhabited space. *)
Definition pointed_cover_space (T : topologicalType) (x : T) : Type := T.

Section WithPoint.
Variable T : topologicalType.
Variable x : T.
Local Notation P := (pointed_cover_space x).
#[local] HB.instance Definition _ := Choice.copy P T.
#[local] HB.instance Definition _ := isPointed.Build P x.
#[local] HB.instance Definition _ := Topological.copy P T.

(** Source for [compact_open_cover_with_point]: Federer
    2.2.5, p. 63, finite-subcover step; supporting adapter from
    the general-topology compactness theorem when an ambient point
    is supplied. The point is not a hypothesis of Radon regularity. *)
Lemma compact_open_cover_with_point (J : choiceType) (D : set J)
    (F : J -> set T) K : compact K ->
  (forall j, D j -> open (F j)) -> K `<=` \bigcup_(j in D) F j ->
  finite_subset_cover D F K.
Proof.
move=> hK ho hc.
have hKP : @compact [the topologicalType of P] K := hK.
rewrite (@compact_cover [the ptopologicalType of P]) in hKP.
exact: hKP J D F ho hc.
Qed.
End WithPoint.

(** Source for [compact_open_finite_cover]: Federer
    2.2.5, p. 63, supporting finite-subcover theorem, including
    an empty ambient space or an empty compact set. General topology
    supplies the nonempty case; the empty case uses the empty subcover. *)
Lemma compact_open_finite_cover (T : topologicalType) (J : choiceType)
    (D : set J) (F : J -> set T) K : compact K ->
  (forall j, D j -> open (F j)) -> K `<=` \bigcup_(j in D) F j ->
  finite_subset_cover D F K.
Proof.
move=> hK ho hc; case: (pselect (exists x, K x))=> [[x hx]|he].
- exact: (@compact_open_cover_with_point T x J D F K hK ho hc).
- exists fset0; first by move=> j; rewrite inE.
  move=> x hx; exfalso; apply: he; by exists x.
Qed.
