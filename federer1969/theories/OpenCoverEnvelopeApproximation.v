(** Federer (1969), 2.5.14, p. 108: choose an open W containing T whose
    alpha cost is arbitrarily close to Phi(T). This is a consequence of the
    abstract infimum laws alone. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import OpenCoverContentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [open_cover_envelope_strict_approximation]: the open superset
    W chosen in Federer 2.5.14, p. 108 *)
Lemma open_cover_envelope_strict_approximation (R : realType) (X : topologicalType)
    (a nu : set X -> \bar R) (hn : is_open_cover_envelope a nu) S c :
  nu S < c -> exists V, open V /\ S `<=` V /\ a V < c.
Proof.
move=> hc; apply: contrapT=> hnV.
have hb : c <= nu S.
  apply: (open_cover_envelope_greatest hn)=> V hV hSV.
  rewrite leNgt; apply/negP=> hv; apply: hnV; exists V; split=> //; by split.
by move: hc; rewrite ltNge hb.
Qed.
