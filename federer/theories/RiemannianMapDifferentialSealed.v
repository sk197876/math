(** Federer (1969), 3.2.46, p. 282: seal the
    proved partial differential of the original chart map.
    Downstream proofs see only its exact graph specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom GrassmannAbbreviations RiemannianTensorUP
  RiemannianMetricCarrier PartialFunctionUP RiemannianMapDifferentialUP
  RiemannianMapDifferentialConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type RiemannianMapDifferentialSignature.
(** Source for [value]: the partial coordinate differential
    used in Federer 3.2.46, p. 282. *)
Parameter value : forall (R : realType) m n A B g h
  (hg : @is_continuous_riemannian_tensor R m A g)
  (hh : @is_continuous_riemannian_tensor R n B h),
  (riemannian_metric_space hg -> riemannian_metric_space hh) ->
  partial_function (riemannian_metric_space hg) (Hom (R_n R m) (R_n R n)).
(** Source for [laws]: exact original-coordinate graph,
    supporting Federer 3.2.46, p. 282. *)
Parameter laws : forall (R : realType) m n A B g h
  (hg : @is_continuous_riemannian_tensor R m A g)
  (hh : @is_continuous_riemannian_tensor R n B h)
  (f : riemannian_metric_space hg -> riemannian_metric_space hh),
  is_riemannian_map_differential_graph f (@value R m n A B g h hg hh f).
End RiemannianMapDifferentialSignature.

Module RiemannianMapDifferential : RiemannianMapDifferentialSignature.
(** Source for [value]: private selection from the proved
    existence of the graph in 3.2.46, p. 282. *)
Definition value (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :=
  projT1 (cid (riemannian_map_differential_graph_exists f)).
(** Source for [laws]: the selected graph satisfies the
    independent laws for 3.2.46, p. 282. *)
Lemma laws (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :
  is_riemannian_map_differential_graph f (@value R m n A B g h hg hh f).
Proof. exact: projT2 (cid (riemannian_map_differential_graph_exists f)). Qed.
End RiemannianMapDifferential.
