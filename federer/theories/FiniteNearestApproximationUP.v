(** Federer (1969), 2.4.12, p. 87: finite-image density, with the erratum p.
    2, book p. 87 line 18, requiring p<infinity or finite-dimensional
    target. The supporting specification here uses nearest points among
    finite prefixes of a supplied sequence, including zero. This gives
    finite Borel partitions and a pointwise norm majorant for dominated
    convergence. It is a proof detail, not an extra assertion attributed to
    Federer. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import BorelDiscreteIndexUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_finite_nearest_approximation]: supporting abstract
    finite-partition specification for the density assertion in Federer
    2.4.12, p. 87. Each label chooses a nearest point among the first n+1
    candidates; ties are unrestricted, and every label fibre is Borel. *)
Record is_finite_nearest_approximation (R : realType) (Y : metricType R)
    (y : nat -> Y) (q : nat -> Y -> nat) : Prop := {
  (** Source for [finite_nearest_index_bound]: finite range needed
      for Federer 2.4.12, p. 87, finite-image density. *)
  finite_nearest_index_bound : forall n x, (q n x <= n)%N;
  (** Source for [finite_nearest_fibres]: Borel partition property supporting
    Federer 2.4.12, p. 87 *)
  finite_nearest_fibres : forall n, has_borel_index_fibres (q n);
  (** Source for [finite_nearest_minimal]: nearest-point error control
      supporting the dominated approximation argument for Federer 2.4.12,
      p. 87. Zero as a candidate bounds the error by the input norm. *)
  finite_nearest_minimal : forall n x i, (i <= n)%N ->
    mdist x (y (q n x)) <= mdist x (y i)
}.
