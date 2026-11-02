(** Federer (1969), 2.3.7, pp. 77–78: uniform convergence on the large
    measurable set B. The erratum p. 1, book p. 78 line 7, concerns the
    opening of 2.3.8, not Egoroff's theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [partial_function_uniformly_converges_on]: direct
    uniform convergence conclusion of Federer 2.3.7, pp. 77–78.
    All values are defined on B; the index after which the distance
    is small is independent of the source point. *)
Record partial_function_uniformly_converges_on (R : realType) (X : Type)
    (Y : metricType R) (B : set X) (f : nat -> partial_function X Y)
    (g : partial_function X Y) : Prop := {
  (** Source for [uniform_partial_domain]: Supporting Federer 2.3.7, p. 77. *)
  uniform_partial_domain : B `<=` partial_function_domain g `&` (\bigcap_n partial_function_domain (f n));
  (** Source for [uniform_partial_distance]: the uniform metric
      bound in Federer 2.3.7, pp. 77–78. *)
  uniform_partial_distance : forall e : R, 0 < e -> exists N,
    forall n, (N <= n)%N -> forall x y z, B x ->
      partial_function_graph (f n) x y -> partial_function_graph g x z -> mdist y z < e
}.
