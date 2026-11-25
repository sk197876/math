(** Federer (1969), 4.1.12, p. 369: the
    smooth functions used in the second example
    have values in [0,1], the specified unit
    value, compact support and the exact derivative
    bound. Specify a common unit-scale function
    independently; regularisation will prove existence. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormRegularity GrassmannAbbreviations
  EuclideanInnerProduct EuclideanOneCoordinate InnerNorm HilbertFormCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_current_unit_interval_cutoff]: a
    smooth unit-scale cutoff inside (0,4), with
    value one at 2, values in [0,1]
    and Lipschitz constant one. Translation and
    positive scaling give the original phi_k of
    Federer 4.1.12, p. 369. The interval
    [1/4,15/4] leaves an explicit support margin. *)
Definition is_current_unit_interval_cutoff (R:realType) (f:R_n R 1%N->R^o):Prop:=
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R 1%N))
    (@scalar_absolute_value_norm R) (fun _=>True) f /\
  (forall x,0<=f x<=1) /\
  (forall x y,`|f x-f y|<=inner_norm (@euclidean_inner_productP R 1%N) (x-y)) /\
  f (euclidean_one_embed 2)= 1 /\
  forall x,~(1/4<=euclidean_one_project x<=15/4)->f x=0.
