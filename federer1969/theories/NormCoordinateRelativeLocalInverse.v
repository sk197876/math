(** Federer (1969), 3.4.8(10), p. 332:
    use the proved analytic coordinate system
    as the actual local inverse chart
    in the finite-fibre argument. All
    topological conclusions follow from the
    existing class and cancellation laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormClassOneUP NormRegularity
  NormClassZeroTopology NormCoordinateSystemUP RelativeLocalInverseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [norm_coordinate_relative_local_inverse]:
    p_m restricted to Z intersect U
    maps homeomorphically onto V, supporting
    3.4.8(10), p. 332. Openness
    and inverse continuity are derived from
    the actual class predicates, with no
    topology imposed on points outside the domains. *)
Theorem norm_coordinate_relative_local_inverse (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (Z U:set X) (V:set Y) (P:X->Y) (psi:Y->X) k a:
  Z a ->U a ->is_norm_coordinate_system hNX hNY Z U V P psi k ->
  @is_relative_local_inverse (Topological.clone (real_norm_metric_space hNX) _)
    (Topological.clone (real_norm_metric_space hNY) _) P Z a U V psi.
Proof.
move=>ha hUa hChart.
have hForward:=norm_class_continuous (norm_coordinate_class_forward hChart).
have hBackward:=norm_class_continuous (norm_coordinate_class_backward hChart).
split;first exact:hUa.
split;first exact:(@norm_class_zero_domain_open R X Y NX NY hNX U P hForward).
split;first exact:(@norm_class_zero_domain_open R Y X NY NX hNY V psi hBackward).
split;first exact:(norm_coordinate_forward_range hChart hUa).
split.
- move=>y hy;have h:=norm_coordinate_backward_membership hChart hy.
  split;first exact:h.1.
  split;first exact:h.2.
  exact:(@norm_coordinate_cancel R X Y NX NY hNX hNY Z U V P psi k hChart y hy).
split.
- move=>x hx hUx;exact:(@norm_coordinate_base_inverse R X Y NX NY hNX hNY Z U V P psi k hChart x hx hUx).
- move=>y hy;exact:(@norm_class_zero_continuous_at R Y X NY NX hNY hNX V psi y hBackward hy).
Qed.
