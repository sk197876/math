(** Federer (1969), 2.2.11, p. 68: project the universal closed set for Y
    times N to obtain the universal Suslin set. Reordering the two sequence
    coordinates gives the required closed witness in (Y times N) times N.
    Erratum p. 1, book p. 68 line 14, supplies the corrected ambient space.
    Source context: CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace SuslinSetUP TopologicalProductMaps
  UniversalClosedSetUP UniversalSuslinSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [universal_suslin_relation]: private projection
    formula for S in Federer 2.2.11, p. 68. The first
    sequence coordinate is existentially quantified; the second
    remains the parameter selecting the Suslin slice. *)
Definition universal_suslin_relation (R : realType) (T : topologicalType)
    (C : set ((T * positive_sequence_space R) * positive_sequence_space R)) :
    set (T * positive_sequence_space R) :=
  [set p | exists m, C ((p.1,m),p.2)].

(** Source for [universal_suslin_relation_is_suslin]: direct
    Suslin assertion for S in Federer 2.2.11, p. 68,
    by a closed witness obtained through continuous coordinate
    permutation. No countability property of T is needed here. *)
Lemma universal_suslin_relation_is_suslin (R : realType) (T : topologicalType)
    (C : set ((T * positive_sequence_space R) * positive_sequence_space R)) :
  closed C -> is_suslin_set R (universal_suslin_relation C).
Proof.
move=> hC.
pose F (p : (T * positive_sequence_space R) * positive_sequence_space R) :=
  ((p.1.1,p.2),p.1.2).
have hF : continuous F.
  apply: topological_pair_continuous.
  - apply: topological_pair_continuous.
    + move=> p; exact (continuous_comp
        (@first_projection_continuous [the topologicalType of (T * positive_sequence_space R)%type] (positive_sequence_space R) p)
        (@first_projection_continuous T (positive_sequence_space R) p.1)).
    + exact: second_projection_continuous.
  - move=> p; exact (continuous_comp
      (@first_projection_continuous [the topologicalType of (T * positive_sequence_space R)%type] (positive_sequence_space R) p)
      (@second_projection_continuous T (positive_sequence_space R) p.1)).
exists (F @^-1` C); split.
- exact: (proj1 (continuous_closedP F) hF C hC).
- apply/seteqP; split.
  + move=> [x n] [[[y k] m] h <-]; by exists m.
  + move=> [x n] [m hm]; by exists ((x,n),m).
Qed.

(** Source for [universal_suslin_relation_laws]: direct slice
    universality assertion for S in Federer 2.2.11, p. 68:
    a closed witness for any Suslin A is a slice of the
    universal closed set, and projecting that slice gives A. *)
Lemma universal_suslin_relation_laws (R : realType) (T : topologicalType)
    (C : set ((T * positive_sequence_space R) * positive_sequence_space R)) :
  is_universal_closed_set C -> is_universal_suslin_set (universal_suslin_relation C).
Proof.
move=> hC; constructor.
- apply: universal_suslin_relation_is_suslin; exact: universal_closed_set_closed hC.
- move=> A [D [hD hDA]].
  have [n hn] := @universal_closed_set_slices R [the topologicalType of (T * positive_sequence_space R)%type] C hC D hD.
  exists n; rewrite -hDA; apply/seteqP; split.
  + move=> x [[y m] hm <-]; exists m; by move: hm; rewrite hn.
  + move=> x [m hm]; exists (x,m)=> //; by rewrite hn.
Qed.
