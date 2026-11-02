(** Federer (1969), 3.2.20, p. 256: the approximate Jacobian
    is the exterior norm of the actual partial approximate differential.
    Degree and measure-density dimension are separate for later use in
    3.2.22, p. 258. Existence and opaque selection are separate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness PartialFunctionUP MeasureApproximateDifferentialUP PartialExteriorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [has_measure_approximate_jacobian]: the displayed formula
    ap J_m f(w)=norm(exterior^m ap Df(w)) in Federer 3.2.20,
    p. 256. The norm is specified using only actual partial
    differential values. An actual approximate differential is required,
    so no default value is assigned off its domain, even in degree zero.
    Separate density dimension m and exterior degree q support the
    approximate mu-dimensional Jacobian in 3.2.22, p. 258. *)
Definition has_measure_approximate_jacobian (R : realType) n k
    (phi : set (R_n R n) -> \bar R) m q
    (f : partial_function (R_n R n) (R_n R k)) a (J : R) : Prop :=
  exists d : partial_function (R_n R n) (R_n R k),
    is_measure_approximate_differential (inner_norm (@euclidean_inner_productP R k))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) phi m f a d /\
    is_partial_exterior_norm q d J.

(** Source for [is_measure_approximate_jacobian_graph]: exact partial
    graph of the approximate Jacobian in Federer 3.2.20, p. 256,
    and its lower-degree version in 3.2.22, p. 258. Its
    existence is proved from the independently stated differential and
    norm laws; it is not an unproved project axiom. *)
Definition is_measure_approximate_jacobian_graph (R : realType) n k
    (phi : set (R_n R n) -> \bar R) m q
    (f : partial_function (R_n R n) (R_n R k))
    (J : partial_function (R_n R n) R) : Prop :=
  forall a j, partial_function_graph J a j <-> has_measure_approximate_jacobian phi m q f a j.
