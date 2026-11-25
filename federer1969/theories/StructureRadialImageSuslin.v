(** Federer (1969), 3.3.4, p. 291: each
    original image R_v is Suslin. This is
    the actual Borel-image theorem 2.2.14,
    p. 70, applied to the original source,
    its strict radius ball and the map domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import SuslinSetUP CompleteMetricUP BorelFunctionUP
  BorelSuslinImages BorelClosedProjection TopologicalBorel MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_radial_original_image_suslin]:
    Suslinness of the original R_v in Federer
    3.3.4, p. 291. The partial direction map
    is represented by a Borel extension whose
    actual source domain D is retained in
    the original image; no hull is substituted. *)
Theorem structure_radial_original_image_suslin (R:realType) (X Y:metricType R)
    (A D:set X) (a:X) (delta:R) (f:X->Y):
  is_complete_metric_space X ->is_complete_metric_space Y ->
  (exists C:set X,countable C /\dense C) ->
  (exists C:set Y,countable C /\dense C) ->
  is_suslin_set R A ->borel_set D ->is_borel_function f ->
  is_suslin_set R (f @` [set x|A x /\ mdist a x<delta /\ D x]).
Proof.
move=>hX hY hSX hSY hA hD hF.
apply:(borel_function_suslin_image hX hY hSX hSY hF).
have he:[set x:X|A x /\ mdist a x<delta /\ D x]=
    A `&` ([set x|mdist a x<delta] `&` D).
  by apply/seteqP; split=>x [hAx [hNear hDx]]; repeat split.
rewrite he; apply:suslin_binary_intersection=>//.
apply:suslin_binary_intersection.
- apply:metric_borel_suslin; apply:open_borel_set; exact:metric_open_ball_open.
- exact:metric_borel_suslin hD.
Qed.
