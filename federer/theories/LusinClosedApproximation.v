(** Federer (1969), 2.3.5, pp. 76–77: Lusin's theorem from closed inner
    approximation. Source context: LusinPiecesUP.v. This supporting
    formulation isolates precisely the measure/topology input common to the
    metric and Radon cases of the printed theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialContinuityUP MeasureUP
  MeasurableFunctionUP ClosedApproximationUP LusinPiecesUP LusinFinitePieces
  LusinClosedLimit GeometricErrorBudget.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [lusin_closed_approximation]: supporting abstract
    form of Federer 2.3.5, pp. 76–77. Separate finite-piece
    approximations use summable measure errors and reciprocal image
    diameters; their common closed intersection carries continuity. *)
Theorem lusin_closed_approximation (R : realType) (X : topologicalType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (D : set Y) (A : set X) (f : partial_function X Y) (epsilon : R) :
  countable D -> dense D ->
  (forall K, closed K -> measure_measurable mu K) ->
  (forall H, measure_measurable mu H -> mu H < +oo -> is_closed_approximable mu H) ->
  is_measure_measurable_function mu f -> measure_measurable mu A -> mu A < +oo ->
  (0 < epsilon)%R -> exists C, closed C /\ C `<=` A /\
    mu (A `\` C) < epsilon%:E /\ partial_function_continuous_on C f.
Proof.
move=> hc hd hclosed happ hf hA hfin he.
have hex i : exists p : nat * (nat -> set X),
    is_lusin_piece_system mu A f ((i.+1)%:R)^-1
      (geometric_error_budget epsilon i) p.1 p.2.
  have hi : (0 < ((i.+1)%:R : R)^-1)%R by rewrite invr_gt0 ltr0n.
  have [N [E hE]] := @lusin_finite_closed_pieces R X Y mu hm D A f _ _
    hc hd hclosed happ hf hA hfin hi (geometric_error_budget_positive i he).
  by exists (N,E).
pose p i := projT1 (cid (hex i)).
have hp i : is_lusin_piece_system mu A f ((i.+1)%:R)^-1
    (geometric_error_budget epsilon i) (p i).1 (p i).2.
  exact: projT2 (cid (hex i)).
exact (@lusin_piece_sequence_limit R X Y mu hm A f epsilon
  (fun i => (p i).1) (fun i => (p i).2) he hp).
Qed.
