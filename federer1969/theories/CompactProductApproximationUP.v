(** Federer (1969), 2.6.4, p. 119: finite sums from K(X) tensor K(Y), used
    for uniqueness of the product Daniell functional. We record an actual
    finite separated-product presentation. *)
From mathcomp Require Import all_boot all_algebra finmap classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope fset_scope.

(** Source for [is_finite_compact_separated_sum]: supporting
    finite-sum description of the top-arrow image in the final
    diagram of Federer 2.6.4, p. 119. The finite
    index set consists of points of Y, as in the section-sampling
    approximation; an empty index set represents zero. *)
Definition is_finite_compact_separated_sum (R : realType) (X Y : topologicalType)
    (h : (X*Y) -> R) :=
  exists (F : {fset Y}) (a : Y -> X -> R) (b : Y -> Y -> R),
    (forall j, j \in F -> compactly_supported_continuous_functions (a j) /\
      compactly_supported_continuous_functions (b j)) /\
    forall p, h p=\sum_(j <- F) a j p.1*b j p.2.
