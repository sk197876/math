(** Federer (1969), 3.2.31, p. 269: supporting finite compact
    refinements for summing the locally rescaled fibre estimates.
    Null overlaps preserve the exact source mass, avoiding any
    factor depending on the number of covering neighborhoods. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal topology.
From Federer Require Import MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_finite_compact_null_overlap_cover]: supporting
    compact-piece formulation of the summation in Federer 3.2.31,
    p. 269. Pieces cover exactly K, lie in the prescribed closed
    neighborhoods, and have measure-zero pairwise overlaps. The
    laws specify the cover before its existence is established. *)
Record is_finite_compact_null_overlap_cover (R:realType) (X:topologicalType)
    (mu:set X->\bar R) (K:set X) (N:nat) (C D:nat->set X):Prop:={
  (** Source for [null_overlap_cover_compact]: supporting compact pieces
      in Federer 3.2.31, p. 269; this proof route retains compact fibres. *)
  null_overlap_cover_compact:forall i,(i<N)%N ->compact (D i);
  (** Source for [null_overlap_cover_subordinate]: supporting local
      rescaling neighborhoods in Federer 3.2.31, p. 269. *)
  null_overlap_cover_subordinate:forall i,(i<N)%N ->D i `<=` K `&` C i;
  (** Source for [null_overlap_cover_union]: supporting exact source
      coverage for the sum in Federer 3.2.31, p. 269. *)
  null_overlap_cover_union:(\bigcup_(i in [set i|(i<N)%N]) D i)=K;
  (** Source for [null_overlap_cover_pairwise_null]: supporting the
      additive source-mass bound in Federer 3.2.31, p. 269, via
      the null-overlap consequence of 2.1.3, p. 55. *)
  null_overlap_cover_pairwise_null:forall i j,(i<N)%N ->(j<N)%N ->i!=j ->
    mu (D i `&` D j)=0
}.
