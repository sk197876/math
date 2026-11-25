(** Federer (1969), 2.3.2(2), p. 73: supporting openness of the interval
    family used by the ray criterion and its product applications. Source
    context: CountableOrderIntervals.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets topology.
From Federer Require Import CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [order_family_interval_open]: supporting openness
    of the dense-endpoint basic intervals for Federer 2.3.2(2),
    p. 73. Either or both endpoints may be absent. *)
Lemma order_family_interval_open disp (Y : orderTopologicalType disp)
    (J : Type) (d : J -> Y) c : open (order_family_interval d c).
Proof.
have he : order_family_interval d c =
    (if c.1 is Some j then [set y | (d j < y)%O] else setT) `&`
    (if c.2 is Some j then [set y | (y < d j)%O] else setT) by case: c=> [[j|] [k|]].
rewrite he; clear he; apply: openI.
- case: c=> [[j|] [k|]] /=; first [exact: order_strict_upper_ray_open | exact: openT].
- case: c=> [[j|] [k|]] /=; first [exact: order_strict_lower_ray_open | exact: openT].
Qed.
