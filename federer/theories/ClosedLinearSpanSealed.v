(** Opaque interface for the closed linear span supporting Federer (1969),
    2.3.8, p. 78. Source context: ClosedLinearSpanUP.v. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric ClosedLinearSpanUP
  ClosedLinearSpanConstruction SeparableClosedLinearSpanConstruction MetricSubsetBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type ClosedLinearSpanSignature.
(** Source for [value]: abstract closed linear span supporting
    Federer 2.3.8, p. 78; no intersection formula is exposed. *)
Parameter value : forall (R : realType) (V : lmodType R)
  (N : V -> R) (hN : is_real_norm N), set (real_norm_metric_space hN) -> subspace V.
(** Source for [laws]: universal property of the supporting closed
    linear span in Federer 2.3.8, p. 78. *)
Parameter laws : forall (R : realType) (V : lmodType R)
  (N : V -> R) (hN : is_real_norm N) (D : set (real_norm_metric_space hN)),
  is_closed_linear_span D (@value R V N hN D).
(** Source for [countable_separable]: separability of the closed span of
    countably many generators supporting Federer 2.3.8, p. 78 *)
Parameter countable_separable : forall (R : realType) (V : lmodType R)
  (N : V -> R) (hN : is_real_norm N) (D : set (real_norm_metric_space hN)),
  countable D -> exists E : set (metric_subset
    (fun y : real_norm_metric_space hN => @value R V N hN D y)),
    countable E /\ dense E.
End ClosedLinearSpanSignature.

Module ClosedLinearSpan : ClosedLinearSpanSignature.
(** Source for [value]: private choice of the proved span witness
    supporting Federer 2.3.8, p. 78. *)
Definition value (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (D : set (real_norm_metric_space hN)) :=
  projT1 (cid (@closed_linear_span_exists R V N hN D)).
(** Source for [laws]: verification of the abstract span laws
    supporting Federer 2.3.8, p. 78. *)
Lemma laws (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (D : set (real_norm_metric_space hN)) :
  is_closed_linear_span D (value D).
Proof. exact: projT2 (cid (@closed_linear_span_exists R V N hN D)). Qed.
(** Source for [countable_separable]: verification of the
    countable-span separability promise supporting Federer 2.3.8,
    p. 78. Only existence and the span specification are used
    to identify the selected witness. *)
Lemma countable_separable (R : realType) (V : lmodType R)
  (N : V -> R) (hN : is_real_norm N) (D : set (real_norm_metric_space hN)) :
  countable D -> exists E : set (metric_subset
    (fun y : real_norm_metric_space hN => value D y)), countable E /\ dense E.
Proof.
move=> hd; exact (@closed_linear_span_countable_separable_exists R V N hN D
  (value D) hd (laws D)).
Qed.
End ClosedLinearSpan.
