(** Federer (1969), 3.2.46, p. 282: public actual
    map differential. It retains the original chart and
    map, independent of the local coordinate extensions. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations RiemannianTensorUP
  RiemannianMetricCarrier PartialFunctionUP RiemannianMapDifferentialUP
  RiemannianMapDifferentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [riemannian_map_differential]: the actual
    partial coordinate differential Df in 3.2.46, p. 282,
    exposed solely through the independently specified laws. *)
Definition riemannian_map_differential (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :=
  @RiemannianMapDifferential.value R m n A B g h hg hh f.

(** Source for [riemannian_map_differential_graph]: exact
    original-domain differential graph from 3.1.1, p. 209,
    supporting the Riemannian formulas of 3.2.46, p. 282. *)
Theorem riemannian_map_differential_graph (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) a D :
  partial_function_graph (riemannian_map_differential f) a D <->
    has_riemannian_map_differential f a D.
Proof. exact: RiemannianMapDifferential.laws. Qed.
