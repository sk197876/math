(** Federer (1969), 3.1.22, pp. 235–236: differentiation
    relative to a subset. The derivative has exactly the tangent
    cone as domain; an ambient linear extension is auxiliary. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP PartialFunctionUP TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_tangent_differential_restriction]: L is
    Dg(a) restricted to Tan(S,a), in the definition of
    Federer 3.1.22, p. 235. The graph has exactly
    the tangent cone as domain, rather than arbitrarily defined
    values on the rest of the ambient vector space. *)
Definition is_tangent_differential_restriction (R:realType) (X Y:lmodType R)
    (NX:X->R) (S:set X) a (D:Hom X Y) (L:partial_function X Y) :=
  forall v y,partial_function_graph L v y <-> norm_tangent_cone NX S a v /\ D v=y.

(** Source for [has_relative_norm_differential]: the definition
    of relative differentiability and its differential in Federer
    3.1.22, p. 235. An ambient differentiable extension
    agrees with f on S in a neighbourhood of a. A is
    the actual domain of f; a need only lie in Clos S. *)
Definition has_relative_norm_differential (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX)
    (A S:set X) (f:X->Y) a (L:partial_function X Y) :=
  @closure (real_norm_metric_space hNX) S a /\
  exists (U:set X) (g:X->Y) (D:Hom X Y),
    has_norm_differential NX NY U g a D /\
    (forall x,S x -> U x -> A x /\ f x=g x) /\
    is_tangent_differential_restriction NX S a D L.

(** Source for [relative_norm_differentiable_at]: existence of
    a differential relative to S at a, Federer 3.1.22,
    p. 235; no ambient extension or derivative is postulated. *)
Definition relative_norm_differentiable_at (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (A S:set X) (f:X->Y) a :=
  exists L,@has_relative_norm_differential R X Y NX NY hNX A S f a L.

(** Source for [is_relative_norm_differential_graph]: the
    notation Df(a) for the unique relative differential in
    Federer 3.1.22, p. 235, specified by its
    exact graph before an opaque witness is selected. *)
Definition is_relative_norm_differential_graph (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (A S:set X) (f:X->Y)
    (D:partial_function X (partial_function X Y)) :=
  forall a L,partial_function_graph D a L <-> @has_relative_norm_differential R X Y NX NY hNX A S f a L.

(** Source for [has_relative_first_order_approximation]: the
    epsilon form of the displayed relative remainder criterion
    in Federer 3.1.22, p. 235. The erratum p. 4,
    book p. 235 line 19 requires f(a)=eta when a is
    in S. The actual f-domain must contain S locally. *)
Definition has_relative_first_order_approximation (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (A S:set X) (f:X->Y) a eta (D:Hom X Y) :=
  norm_bounded_linear NX NY D /\
  (S a -> f a=eta) /\
  (exists r:R,0<r /\ forall x,S x -> NX (x-a)<r -> A x) /\
  forall e:R,0<e -> exists d:R,0<d /\ forall x,S x ->
    0<NX (x-a) -> NX (x-a)<d -> NY (f x-eta-D (x-a))<=e*NX (x-a).
