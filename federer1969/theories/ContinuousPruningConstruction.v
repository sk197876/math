(** Federer (1969), 2.10.23, p. 186: private existence proof for coordinate
    pruning with the approximating measure, using 2.10.22 in place of
    regularity. The recursion and geometric loss laws are exactly the
    existing specification for 2.2.12, p. 69. Only the source projection has
    to have finite mass. Source context and the new continuity abstraction:
    IncreasingProjectionLoss.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import SequenceSpace SequenceFiniteBounds CoordinatePruningUP MeasurePruningUP
  MeasureUP MeasureBasic IncreasingProjectionLoss GeometricErrorBudget.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section Construction.
Variables (R : realType) (X : topologicalType) (gamma : set X -> \bar R).
Variables (hm : is_measure gamma) (hcont : has_increasing_set_continuity gamma).
Variables (e : R) (he : (0<e)%R).

(** Source for [continuous_pruning_next_bound]: private
    coordinate choice for 2.10.23, p. 186.
    The arbitrary zero outside the finite-projection
    domain only totalises this private recursion;
    every used stage is proved to lie in that domain. *)
Definition continuous_pruning_next_bound k (W : set (X*positive_sequence_space R)) :=
  if pselect (gamma (fst @` W)< +oo) is left hf then
    projT1 (cid (@increasing_projection_coordinate_approximation R X gamma W k
      (geometric_error_budget e k) hm hcont hf (geometric_error_budget_positive k he)))
  else 0%N.

(** Source for [continuous_pruning_next_loss]: supporting
    proved choice law on the finite domain used
    in 2.10.23, p. 186. No value outside
    that domain enters the mathematical argument. *)
Lemma continuous_pruning_next_loss k W : gamma (fst @` W)< +oo ->
  gamma (fst @` W)<gamma (fst @` (W `&`
    [set p | sequence_coordinate_bound k (continuous_pruning_next_bound k W) p.2]))+
      (geometric_error_budget e k)%:E.
Proof.
move=> hf; rewrite /continuous_pruning_next_bound; case: pselect=> [hfin|hnot].
- exact: projT2 (cid (@increasing_projection_coordinate_approximation R X gamma W k
    (geometric_error_budget e k) hm hcont hfin (geometric_error_budget_positive k he))).
- exact: False_ind _ (hnot hf).
Qed.

(** Source for [continuous_pruning_witness_stage]: private
    witness recursion for 2.10.23, p. 186,
    imposing exactly one further coordinate bound at
    every stage as in 2.2.12, p. 69. *)
Fixpoint continuous_pruning_witness_stage (Z : set (X*positive_sequence_space R)) n :=
  match n with
  | 0%N => Z
  | k.+1 => let W := continuous_pruning_witness_stage Z k in
      W `&` [set p | sequence_coordinate_bound k (continuous_pruning_next_bound k W) p.2]
  end.

(** Source for [continuous_pruning_stage_subset]: supporting
    finite-domain proof for the choices of 2.10.23,
    p. 186: every stage retains only original
    witness points, so its projection mass stays finite. *)
Lemma continuous_pruning_stage_subset Z n : continuous_pruning_witness_stage Z n `<=` Z.
Proof. elim: n=> [|n ih] x hx; [exact hx|exact: ih x hx.1]. Qed.

(** Source for [continuous_coordinate_pruning_exists]: supporting
    existence of all Z_i choices in 2.10.23,
    p. 186. The only continuity premise is
    actual continuity below; regularity of the cutoff
    approximation is not assumed. *)
Theorem continuous_coordinate_pruning_exists (Z : set (X*positive_sequence_space R)) :
  gamma (fst @` Z)< +oo -> exists b F, is_measure_coordinate_pruning gamma Z e b F.
Proof.
move=> hZ.
pose F := continuous_pruning_witness_stage Z.
pose b k := continuous_pruning_next_bound k (F k).
exists b,F; constructor.
- constructor=> //.
- exact he.
- move=> k; apply: continuous_pruning_next_loss.
  apply: le_lt_trans _ hZ; apply: (@measure_mono R X gamma hm).
  move=> x [p hp <-]; exists p=> //; exact: continuous_pruning_stage_subset hp.
Qed.
End Construction.
