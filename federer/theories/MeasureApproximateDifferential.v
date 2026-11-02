(** Federer (1969), 3.2.16, p. 253:
    public approximate differential, specified on
    exactly the approximate tangent cone. Only
    the opaque graph laws are used downstream. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP PartialFunctionUP MeasureUP
  MeasureApproximateTangentUP MeasureApproximateDifferentialUP
  MeasureApproximateDifferentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measure_approximate_differential]: the
    notation (phi,m) ap Df(a), Federer 3.2.16,
    p. 253, conditional on actual approximate
    differentiability at a, without a default elsewhere. *)
Definition measure_approximate_differential (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (phi : set X -> \bar R) m (hm : is_measure phi)
    (f : partial_function X Y) a
    (ha : measure_approximately_differentiable_at NY hNX phi m f a) :=
  @MeasureApproximateDifferential.value R X Y NX NY hNX hNY phi m hm f a ha.

(** Source for [measure_approximate_differential_graph]:
    the exact restriction to Tan_m(phi,a) in
    Federer 3.2.16, p. 253. Values arise
    from the proved differentiable representatives. *)
Lemma measure_approximate_differential_graph (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (phi : set X -> \bar R) m (hm : is_measure phi)
    (f : partial_function X Y) a
    (ha : measure_approximately_differentiable_at NY hNX phi m f a) v y :
  partial_function_graph (@measure_approximate_differential R X Y NX NY hNX hNY phi m hm f a ha) v y <->
  measure_approximate_tangent_cone hNX phi m a v /\
    exists D, has_measure_approximate_differential NY hNX phi m f a D /\ D v=y.
Proof. exact: (@MeasureApproximateDifferential.laws R X Y NX NY hNX hNY phi m hm f a ha).2 v y. Qed.

(** Source for [measure_approximate_differential_domain]:
    the domain Tan_m(phi,a) of the approximate
    differential, Federer 3.2.16, p. 253. *)
Lemma measure_approximate_differential_domain (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (phi : set X -> \bar R) m (hm : is_measure phi)
    (f : partial_function X Y) a
    (ha : measure_approximately_differentiable_at NY hNX phi m f a) :
  partial_function_domain (@measure_approximate_differential R X Y NX NY hNX hNY phi m hm f a ha)=
    measure_approximate_tangent_cone hNX phi m a.
Proof.
apply/seteqP; split=> v.
- move=> [y hy].
  exact: ((@measure_approximate_differential_graph R X Y NX NY hNX hNY phi m hm f a ha v y).1 hy).1.
- move=> hv; have [D hD] := ha; exists (D v).
  apply: (@measure_approximate_differential_graph R X Y NX NY hNX hNY phi m hm f a ha v (D v)).2.
  split=> //; exists D; by split.
Qed.
