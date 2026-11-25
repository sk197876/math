(** Federer (1969), 3.3.5, p. 292: independent laws for the
    required global Lipschitz section of an original projection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_structure_projection_section]: the object asserted
    in Federer 3.3.5, p. 292: f is globally s inverse Lipschitz,
    p composed with f is the identity of R^m, and its image contains
    the original subset S. These laws precede the existence proof. *)
Definition is_structure_projection_section (R:realType) n m
    (S:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (s:R)
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):=
  is_metric_lipschitz_bound setT f s^-1 /\
  (forall y,euclidean_projection_linear p (f y)=y) /\ S `<=` f @` setT.
