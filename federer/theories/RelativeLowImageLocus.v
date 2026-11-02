(** Federer (1969), 3.2.33, p. 270: rank loci
    of the actual differential relative to W, independently
    of any choice of analytic coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  PartialFunctionUP RelativeDifferentialUP PartialImageDimensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [relative_low_image_locus]: the intrinsic
    rank threshold used to describe S in Federer 3.2.33,
    p. 270. An actual relative differential has image
    dimension at most mu. Its domain is exactly the
    tangent space; no coordinates, ambient extension or
    differential field are chosen by this definition. *)
Definition relative_low_image_locus (R:realType) n v mu
    (W:set (R_n R n)) (F:R_n R n->R_n R v):set (R_n R n):=
  W `&` [set x|exists d:partial_function (R_n R n) (R_n R v),
    @has_relative_norm_differential R (R_n R n) (R_n R v)
      (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R v))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT W F x d /\
    is_partial_image_dimension_at_most mu d].
