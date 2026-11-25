(** Federer (1969), 3.3.12, p. 297: independent definitions
    of the two hypotheses on each original orthogonal projection. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanLebesgueDimensions MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_projection_preserves_null_subsets]: condition
    (I) of Federer 3.3.12, p. 297. EVERY original subset B of E with
    phi(B)=0 has original projected Lebesgue outer mass zero. No
    measurability or Borel restriction is imposed on these subsets. *)
Definition structure_projection_preserves_null_subsets (R:realType) n m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):Prop:=
  forall B,B `<=` E ->phi B=0 ->
    euclidean_lebesgue_measure m (euclidean_projection_linear p @` B)=0.

(** Source for [structure_projection_almost_finite_fibres]: condition
    (II) of Federer 3.3.12, p. 297. The ORIGINAL E fibre is finite
    at Lebesgue almost every original target point. No source or
    image hull or selected fibre representative is used. *)
Definition structure_projection_almost_finite_fibres (R:realType) n m
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):Prop:=
  measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    [set y|finite_set (E `&` euclidean_projection_linear p @^-1` [set y])].
