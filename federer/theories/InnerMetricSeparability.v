(** Federer (1969), 3.2.26(3), p. 262: supporting
    separability of the finite-dimensional exterior space used
    for the small-orientation partition. This follows from the
    project's finite-basis norm-space background, without importing
    an external vector-space or measure theory. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  LinearBasis InnerSpaceCountableBase CountableBaseDenseSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [finite_inner_metric_separable]: supporting
    finite-dimensional background for Federer 3.2.26(3),
    p. 262. Reindex a finite basis by an ordinal,
    use the proved countable-open-base theorem, and choose
    a dense set through its abstract basis laws. *)
Theorem finite_inner_metric_separable (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (J:finType) (e:J->V):
  is_basis e ->exists D:set (inner_metric_space hB),countable D /\dense D.
Proof.
move=>hBasis.
have hOrdinal:is_basis (fun i:'I_(#|J|)=>e (enum_val i)).
  exact (@basis_reindex R (Choice.clone J _) (Choice.clone 'I_(#|J|) _) V e
    hBasis enum_rank enum_val (@enum_rankK J) (@enum_valK J)).
have [U hU]:=@inner_space_countable_open_base R V B hB #|J|
  (fun i=>e (enum_val i)) hOrdinal.
exact (@countable_open_base_dense_set (inner_metric_space hB) 0 U hU).
Qed.
