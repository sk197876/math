(** Federer (1969), 3.4.2(5), p. 311: the function class Φ and compact
    pieces Ψ. Their laws precede the decomposition existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient GrassmannSubspaces GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric RealNormUP RelativeClassUP
  RelativeDifferential PartialFunctionUP CriticalManifoldFamilyUP
  CriticalOscillation PositiveRightOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_flat_function_class]: Φ(S,C,k) in
    3.4.2(5), p. 311. The map has class k relative to its original
    submanifold domain and vanishes at every point of C. *)
Definition critical_flat_function_class (R:realType) m (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (S C:set (R_n R m))
    (f:R_n R m->Y) k:Prop:=
  norm_class_relative (inner_norm_real_norm (@euclidean_inner_productP R m))
    hNY S S f k /\forall x,C x ->f x=0.

(** Source for [is_critical_flat_piece]: Ψ(S,C,k) in 3.4.2(5), p. 311.
    The piece T has some admissible dimension at most mu; G is compact
    and lies in T intersect C. Its oscillation has limit zero for EVERY
    original class-k function vanishing on C. The same pair works for
    all these functions. *)
Definition is_critical_flat_piece (R:realType) m d (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (Z:G (R_n R m) d) mu
    (S C:set (R_n R m)) k (T G:set (R_n R m)):Prop:=
  (exists gamma,(gamma<=mu)%N /\critical_manifold_family Z gamma 1 T) /\
  T `<=` S /\@compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) G /\
  G `<=` T `&` C /\forall f,critical_flat_function_class hNY S C f k ->
    positive_right_extended_order_limit
      (fun delta=>critical_eta NY (grassmann_val Z) T G f k%:R delta) 0%E.

(** Source for [critical_tangent_zero_locus]: the original set C of
    3.4.2(9), p. 311. Its relative differential is defined and vanishes
    on Z intersect Tan(S,x). The partial graph retains the exact tangent
    domain and leaves other vector values undefined. *)
Definition critical_tangent_zero_locus (R:realType) m (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (Z:subspace (R_n R m))
    (S:set (R_n R m)) (f:R_n R m->Y):set (R_n R m):=
  [set x|S x /\exists D:partial_function (R_n R m) Y,
    partial_function_graph (relative_norm_differential
      (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY S S f) x D /\
    forall z y,Z z ->partial_function_graph D z y ->y=0].

(** Source for [critical_common_tangent_zero_set]: the set B used in
    the proof of 3.4.2(7), pp. 312–313. At its points every original
    function in Φ has derivative zero on the specified tangent vectors.
    The quantifier over functions remains inside the pointwise condition. *)
Definition critical_common_tangent_zero_set (R:realType) m (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (Z:subspace (R_n R m))
    (S C:set (R_n R m)) k:set (R_n R m):=
  [set x|C x /\forall f,critical_flat_function_class hNY S C f k ->
    critical_tangent_zero_locus hNY Z S f x].
