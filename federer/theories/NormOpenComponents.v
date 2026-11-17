(** Federer (1969), 3.4.8(11), pp. 333–335:
    components of an open normed-space set
    are open. Reuse the already proved
    component-boundary exclusion, whose proof uses
    the project's connected norm balls. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormOpenComponentBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [norm_open_components_open]:
    openness of the original base components,
    used with their homeomorphisms in
    3.4.8(11), p. 335. *)
Theorem norm_open_components_open (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:set X) a:
  @open (real_norm_metric_space hNX) A ->
  @open (real_norm_metric_space hNX) (@connected_component (real_norm_metric_space hNX) A a).
Proof.
move=>hOpen;rewrite openE=>x hx.
have hAx:=@connected_component_sub (real_norm_metric_space hNX) A a x hx.
apply:contrapT=>hNotInterior.
exact:(@norm_open_component_boundary_outside R X NX hNX A a x hOpen
  (subset_closure hx) hNotInterior hAx).
Qed.
