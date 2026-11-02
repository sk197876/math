(** Federer (1969), 2.10.23, p. 186: the coordinate-pruning construction of
    2.2.12, p. 69, is performed with the approximating measure, using its
    continuity below proved in 2.10.22. This supporting abstraction states
    the needed continuity law separately from measure regularity. Only the
    current projection needs finite mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import SequenceSpace SequenceFiniteBounds MeasureUP MeasureBasic ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [has_increasing_set_continuity]: supporting
    abstract property supplied by 2.10.22 and
    invoked for the Z_i choices in 2.10.23,
    p. 186. It asserts actual increasing order
    limits on arbitrary subsets; it is not an
    assumption of regularity or measurability. *)
Definition has_increasing_set_continuity (R : realType) (I : choiceType) (gamma : set I -> \bar R) :=
  forall A : nat -> set I, (forall n m, (n<=m)%N -> A n `<=` A m) ->
    extended_increases_to (fun n=>gamma (A n)) (gamma (\bigcup_n A n)).

(** Source for [increasing_projection_coordinate_approximation]: supporting
    single coordinate choice in 2.10.23,
    p. 186, following 2.2.12, p. 69.
    Continuity of the approximating measure replaces
    regularity, and finiteness is needed only for
    the projection of the current witness W. *)
Theorem increasing_projection_coordinate_approximation (R : realType) (X : topologicalType)
    (gamma : set X -> \bar R) (W : set (X*positive_sequence_space R)) k (e : R) :
  is_measure gamma -> has_increasing_set_continuity gamma ->
  gamma (fst @` W)< +oo -> (0<e)%R -> exists m,
    gamma (fst @` W)<gamma (fst @` (W `&` [set p | sequence_coordinate_bound k m p.2]))+e%:E.
Proof.
move=> hm hcont hfinite he.
pose A m := fst @` (W `&` [set p | sequence_coordinate_bound k m p.2]).
have hmono n m (hnm : (n<=m)%N) : A n `<=` A m.
  move=> x [p [hp hb] <-]; exists p=> //; split=> //; exact: leq_trans hb hnm.
have hcover : (\bigcup_m A m)=fst @` W.
  apply/seteqP; split.
  - move=> x [m _ [p [hp _] <-]]; by exists p.
  - move=> x [p hp <-]; exists (positive_sequence_coordinates p.2 k)=> //.
    exists p=> //; split=> //; exact: leqnn.
have hlim := hcont A hmono; rewrite hcover in hlim.
have hfin : gamma (fst @` W) \is a fin_num.
  rewrite ge0_fin_numE; last exact: (@measure_nonnegative R X gamma hm (fst @` W)).
  exact hfinite.
have hlt : gamma (fst @` W)-e%:E<gamma (fst @` W).
  rewrite lte_subel_addr // -{1}[gamma (fst @` W)]adde0 lteD2lE // lte_fin; exact he.
have [m hmnear] := hlim.2.1 _ hlt.
exists m; have hh := hmnear m (leqnn m); by rewrite lte_subel_addr in hh.
Qed.
