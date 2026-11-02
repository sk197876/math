(** Private proved existence witness for Federer
    (1969), 3.2.16, p. 253. Only its
    sealing module and the assumptions audit may
    import this implementation. The graph is the
    restriction of a proved linear representative. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP PartialFunctionUP MeasureUP
  MeasureApproximateTangentUP MeasureApproximateDifferentialUP
  MeasureApproximateDifferentialUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measure_approximate_differential_exists]:
    existence of ap Df(a) from the defining
    differentiable representative, Federer 3.2.16,
    p. 253. The approximate differentiability
    premise is proved separately; no default map
    is assigned at inactive points. *)
Theorem measure_approximate_differential_exists (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (phi : set X -> \bar R) m (f : partial_function X Y) a :
  is_measure phi -> measure_approximately_differentiable_at NY hNX phi m f a ->
  exists d, is_measure_approximate_differential NY hNX phi m f a d.
Proof.
move=> hm [D hD].
have hsingle v y z :
    (measure_approximate_tangent_cone hNX phi m a v /\ D v=y) ->
    (measure_approximate_tangent_cone hNX phi m a v /\ D v=z) -> y=z.
  move=> [_ hy] [_ hz]; exact: (eq_trans (esym hy) hz).
pose d := @Build_partial_function X Y (fun v y =>
  measure_approximate_tangent_cone hNX phi m a v /\ D v=y) hsingle.
exists d; split; first by exists D.
move=> v y; split.
- move=> [hv hy]; split=> //; exists D; by split.
- move=> [hv [E [hE hy]]]; split=> //.
  have heq := @measure_approximate_linear_maps_agree_on_cone R X Y NX NY hNX hNY
    phi m f a D E hm hD hE v hv.
  exact: eq_trans heq hy.
Qed.
