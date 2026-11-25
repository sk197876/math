(** General-topology background for a concrete counterexample to the
    converse in Federer (1969), 2.3.8, p. 78: the compact product of
    countably many two-point discrete spaces. The example uses binary
    cylinders in place of the interval characteristic functions suggested.
    No measure or Cantor-space theorem is imported; only product topology,
    discrete topology and Tychonoff's general compactness theorem are used.
    Source context: MeasurableNormedFunctionUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot finmap boolp classical_sets topology.
From Federer Require Import CompactTube.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_sequence_space]: product-topology background
    supporting the local counterexample to Federer 2.3.8,
    p. 78; the set of infinite sequences of two symbols. *)
Definition binary_sequence_space : Type := prod_topology (fun _ : nat => bool).
HB.instance Definition _ := Pointed.on binary_sequence_space.
HB.instance Definition _ := Nbhs.on binary_sequence_space.
HB.instance Definition _ := Topological.on binary_sequence_space.

(** Source for [binary_sequence_compact]: Tychonoff compactness
    of the binary product, general-topology background for the
    covering construction supporting Federer 2.3.8, p. 78. *)
Lemma binary_sequence_compact : compact (@setT binary_sequence_space).
Proof.
have := @tychonoff _ (fun _ : nat => _) _ (fun=> bool_compact).
by congr (compact _); rewrite eqEsubset.
Qed.

(** Source for [binary_cylinder]: a finite-prefix cylinder, local
    example infrastructure for Federer 2.3.8, p. 78.
    Its assigned covering cost will be 2 to the negative word length. *)
Definition binary_cylinder (w : seq bool) : set binary_sequence_space :=
  [set x | forall k, (k < size w)%N -> x k = nth false w k].

(** Source for [binary_cylinder_empty_word]: the empty word
    imposes no coordinate constraints, supporting the unit total
    mass in the local example for Federer 2.3.8, p. 78. *)
Lemma binary_cylinder_empty_word : binary_cylinder [::] = setT.
Proof. apply/seteqP; split=> // x _ k; by rewrite ltn0. Qed.

(** Source for [binary_cylinder_open]: finite-prefix cylinders
    are open in the product topology, supporting the compact
    finite-subcover argument for the example in Federer 2.3.8,
    p. 78. This is general topology, not an extra book claim. *)
Lemma binary_cylinder_open w : open (binary_cylinder w).
Proof.
have he : binary_cylinder w = \bigcap_(i in [set` [fset i | i : 'I_(size w)]])
    [set x : binary_sequence_space | x i = nth false w i].
  apply/seteqP; split=> x hx.
  - move=> i _; exact: hx (val i) (valP i).
  - move=> k hk; apply: (hx (Ordinal hk)); by rewrite /mkset inE.
rewrite he; apply: finite_open_intersection=> i _.
have hc : continuous (fun x : binary_sequence_space => x i).
  exact: proj_continuous.
have ho : @open [the topologicalType of (bool : Type)] [set b | b = nth false w i] := discrete_open _.
have h := @open_comp [the topologicalType of binary_sequence_space] [the topologicalType of (bool : Type)]
  (fun x => x i) [set b | b = nth false w i] (fun x _ => hc x) ho.
exact h.
Qed.
