(** Federer (1969), 2.3.5, p. 77: intersect the finite unions and let the
    image oscillations tend uniformly to zero. Source context:
    LusinPiecesUP.v. The local oscillation proof is the epsilon-neighborhood
    form of the printed uniform-limit argument; it needs no arbitrarily
    chosen values on empty pieces or outside the partial domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialContinuityUP PartialMetricContinuity
  MeasureUP LusinPiecesUP LusinPieceTopology SetSequenceDisjointification
  ExtendedRealReciprocalBounds GeometricErrorBudget MeasureGeometricCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [lusin_piece_sequence_limit]: the final intersection
    C and continuity conclusion of Federer 2.3.5, p. 77.
    Our summable budgets reserve half the error, preserving the
    strict bound in Federer, including for empty C. *)
Theorem lusin_piece_sequence_limit (R : realType) (X : topologicalType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (A : set X) (f : partial_function X Y) (epsilon : R)
    (N : nat -> nat) (E : nat -> nat -> set X) : (0 < epsilon)%R ->
  (forall i, is_lusin_piece_system mu A f ((i.+1)%:R)^-1
    (geometric_error_budget epsilon i) (N i) (E i)) ->
  exists C, closed C /\ C `<=` A /\ mu (A `\` C) < epsilon%:E /\
    partial_function_continuous_on C f.
Proof.
move=> he hs; pose F i := set_sequence_prefix (E i) (N i).
pose C := \bigcap_i F i.
have hC : closed C.
  apply: closed_bigI=> i _; apply: closed_sequence_prefix=> n hn.
  exact: (@lusin_piece_closed R X Y mu A f _ _ _ _ (hs i) n hn).
have hwithin i : F i `<=` A `&` partial_function_domain f.
  move=> x [n hn hx]; exact: (@lusin_piece_within R X Y mu A f _ _ _ _ (hs i) n hn x hx).
have hCA : C `<=` A by move=> x hx; exact: (hwithin 0%N x (hx 0%N Logic.I)).1.
have hdom : C `<=` partial_function_domain f.
  move=> x hx; exact: (hwithin 0%N x (hx 0%N Logic.I)).2.
exists C; split=> //; split=> //; split.
- apply: (proj2 (@measure_geometric_cover_bound R X mu hm _
    (fun i => A `\` F i) epsilon he _
    (fun i => @lusin_piece_error R X Y mu A f _ _ _ _ (hs i)))).
  move=> x [ha hn]; apply: contrapT=> hnone; apply: hn=> i _.
  apply: contrapT=> hni; apply: hnone; exists i; first exact Logic.I; by split.
- apply: (@partial_metric_local_continuity R X Y C f hdom).
  move=> x y hx hxy e hep.
  have [i hi] := @positive_reciprocal_nat_small R e hep.
  have [n hn hnx] := hx i Logic.I.
  have [V [hV [hxV hv]]] := @lusin_piece_relative_neighborhood R X Y mu A f _ _ _ _ (hs i) n x hn hnx.
  exists V; split=> //; split=> // z w hz hzV hzw.
  have hnz := hv z hzV (hz i Logic.I).
  apply: le_lt_trans _ hi.
  exact: (@lusin_piece_oscillation R X Y mu A f _ _ _ _ (hs i) n hn x z y w hnx hnz hxy hzw).
Qed.
