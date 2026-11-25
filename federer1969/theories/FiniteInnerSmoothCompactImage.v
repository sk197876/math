(** Federer (1969), 3.2.28, pp. 265–267:
    compactness passes through the actual smooth maps
    between the indicated inner-product ambient spaces.
    Continuity is derived from the calculus specification. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  NormMetric NormRegularity NormClassZeroTopology InnerOwnNormTopology HomeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [inner_class_map_compact_image]: the
    compact images used for the Grassmann volume calculations,
    Federer 3.2.28(2),(4), pp. 265,267, by
    ordinary continuity on compact sets. The topology
    agrees exactly with the given inner-product metric. *)
Theorem inner_class_map_compact_image (R:realType) (X Y:lmodType R)
    (BX:X->X->R) (BY:Y->Y->R) (hX:is_inner_product BX) (hY:is_inner_product BY)
    (f:X->Y) k (K:set X):
  norm_class (inner_norm_real_norm hX) (inner_norm_real_norm hY) (fun _=>True) f k ->
  @compact [the topologicalType of inner_metric_space hX] K ->
  @compact [the topologicalType of inner_metric_space hY] (f @` K).
Proof.
move=>hF hK.
pose NX:=real_norm_metric_space (inner_norm_real_norm hX).
pose NY:=real_norm_metric_space (inner_norm_real_norm hY).
have hN:continuous (fun x:NX=>(f x:NY)).
  move=>x; exact:(@norm_class_zero_continuous_at R X Y
    (inner_norm hX) (inner_norm hY) (inner_norm_real_norm hX)
    (inner_norm_real_norm hY) (fun _=>True) f x (norm_class_continuous hF) I).
have hA:continuous (fun x:inner_metric_space hX=>(x:NX)):=
  homeomorphism_continuous (inner_own_norm_homeomorphism hX).
have hB:continuous (fun y:NY=>(y:inner_metric_space hY)):=
  homeomorphism_inverse_continuous (inner_own_norm_homeomorphism hY).
have hC:continuous (fun x:inner_metric_space hX=>(f x:inner_metric_space hY)).
  move=>x; exact:(continuous_comp (hA x) (continuous_comp (hN x) (hB (f x)))).
exact:continuous_compact (continuous_subspaceT hC) hK.
Qed.
