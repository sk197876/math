(** Opaque finite separated approximation supporting Federer (1969), 2.6.4,
    p. 119. Specifications and Source context are in
    CompactProductApproximationUP.v and the annotated existence proof. The
    finite partition implementation is hidden from uniqueness and
    integral-representation arguments. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP CompactCutoffUP CompactProductApproximationUP
  CompactProductApproximationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Module Type CompactProductApproximationSignature.
(** Source for [exists_approximation]: fixed-support approximation
    supporting the final proposition of Federer 2.6.4, p. 119. *)
Parameter exists_approximation : forall (R : realType) (X Y : topologicalType)
    (h : (X*Y) -> R) (K : set X) (L : set Y) (v : Y -> R) (e : R),
  hausdorff_space X -> hausdorff_space Y -> locally_compact (@setT Y) ->
  compactly_supported_continuous_functions h -> compact K ->
  (forall x y, ~(K x /\ L y) -> h (x,y)=0) -> is_compact_cutoff L v -> 0<e ->
  exists q : (X*Y) -> R, is_finite_compact_separated_sum q /\
    (forall x y, ~(K x /\ real_function_support v y) -> q (x,y)=0) /\
    forall p, `|h p-q p|<=e.
End CompactProductApproximationSignature.
Module CompactProductApproximation : CompactProductApproximationSignature.
(** Source for [exists_approximation]: the proved finite-partition
    witness for Federer 2.6.4, p. 119. *)
Lemma exists_approximation (R : realType) (X Y : topologicalType)
    (h : (X*Y) -> R) (K : set X) (L : set Y) (v : Y -> R) (e : R) :
  hausdorff_space X -> hausdorff_space Y -> locally_compact (@setT Y) ->
  compactly_supported_continuous_functions h -> compact K ->
  (forall x y, ~(K x /\ L y) -> h (x,y)=0) -> is_compact_cutoff L v -> 0<e ->
  exists q : (X*Y) -> R, is_finite_compact_separated_sum q /\
    (forall x y, ~(K x /\ real_function_support v y) -> q (x,y)=0) /\
    forall p, `|h p-q p|<=e.
Proof. exact: compact_product_separated_approximation_exists. Qed.
End CompactProductApproximation.
