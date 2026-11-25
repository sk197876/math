(** Federer (1969), 2.2.11, p. 68: the diagonal slice T={n:(n,n) in S} of a
    universal Suslin set is Suslin, whereas its complement is not Suslin and
    T is not Borel. Source context and erratum convention:
    UniversalSuslinSetUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import SequenceSpace SuslinSetUP SuslinPreimages TopologicalProductMaps
  UniversalSuslinSetUP TopologicalBorel BorelClosedProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [universal_suslin_diagonal]: direct diagonal set
    T displayed in Federer 2.2.11, p. 68. It is defined
    from an abstract universal Suslin relation. *)
Definition universal_suslin_diagonal (R : realType)
    (S : set (positive_sequence_space R * positive_sequence_space R)) :=
  [set n | S (n,n)].

(** Source for [universal_suslin_diagonal_suslin]: direct Suslin
    assertion for T in Federer 2.2.11, p. 68: the
    diagonal map is continuous, so its inverse image of S is
    Suslin by the theorem proved in 2.2.10. *)
Lemma universal_suslin_diagonal_suslin (R : realType)
    (S : set (positive_sequence_space R * positive_sequence_space R)) :
  is_universal_suslin_set S -> is_suslin_set R (universal_suslin_diagonal S).
Proof.
move=> hS; apply: (@continuous_preimage_suslin R _ _ (fun n : positive_sequence_space R => (n,n)) S).
- apply: topological_pair_continuous; move=> n; exact: cvg_id.
- exact: universal_suslin_set_suslin hS.
Qed.

(** Source for [universal_suslin_diagonal_complement_not_suslin]:
    direct diagonal contradiction in Federer 2.2.11, p. 68.
    If the complement were a universal slice with parameter m,
    membership at m would be equivalent to its own negation. *)
Theorem universal_suslin_diagonal_complement_not_suslin (R : realType)
    (S : set (positive_sequence_space R * positive_sequence_space R)) :
  is_universal_suslin_set S -> ~ is_suslin_set R (~` universal_suslin_diagonal S).
Proof.
move=> hS hcomp.
have [m hm] := @universal_suslin_set_slices R
  [the topologicalType of positive_sequence_space R] S hS
  (~` universal_suslin_diagonal S) hcomp.
have hn : ~ S (m,m).
  move=> hp; have hh : (~` universal_suslin_diagonal S) m by rewrite hm.
  exact: hh hp.
have hh : (~` universal_suslin_diagonal S) m := hn.
apply: hn;
by rewrite hm in hh.
Qed.

(** Source for [universal_suslin_diagonal_not_borel]: direct
    non-Borel assertion in Federer 2.2.11, p. 68. A
    Borel diagonal would have a Borel and therefore Suslin
    complement, contradicting the diagonal argument. *)
Theorem universal_suslin_diagonal_not_borel (R : realType)
    (S : set (positive_sequence_space R * positive_sequence_space R)) :
  is_universal_suslin_set S -> ~ borel_set (universal_suslin_diagonal S).
Proof.
move=> hS hb; apply: (universal_suslin_diagonal_complement_not_suslin hS).
apply: metric_borel_suslin; exact: borel_set_complement hb.
Qed.
