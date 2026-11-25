(** Federer (1969), 3.4.8(5), p. 328:
    the finite coefficient space has a countable compact
    cover. A common index covers each finite tuple;
    product compactness is general topology. *)
From mathcomp Require Import all_boot all_order boolp classical_sets topology.
From Federer Require Import IncreasingCompactCoverUP IncreasingCompactCoverLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [increasing_compact_cover_finite_product]:
    the original finite coefficient space is a countable
    union of compact products, supporting 3.4.8(5), p. 328.
    The zero-generator coefficient space remains a singleton. *)
Theorem increasing_compact_cover_finite_product (T:topologicalType)
    (S:set T) (K:nat->set T) (I:finType):
  is_increasing_compact_cover S K ->
  @is_increasing_compact_cover (prod_topology (fun _:I=>T))
    [set f|forall i,S (f i)] (fun n=>[set f|forall i,K n (f i)]).
Proof.
move=>hK;constructor.
- move=>n;exact (@tychonoff I (fun _=>T) (fun _=>K n)
    (fun _=>@increasing_compact_cover_compact T S K hK n)).
- move=>n f hf i;exact:(@increasing_compact_cover_contained T S K hK n (f i) (hf i)).
- move=>m n hmn f hf i;exact:(@increasing_compact_cover_monotone T S K hK m n hmn (f i) (hf i)).
- move=>f hf;exact:(@increasing_compact_cover_finite_uniform T S K hK I f hf).
Qed.
