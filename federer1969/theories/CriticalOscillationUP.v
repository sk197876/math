(** Federer (1969), 3.4.2(4), pp. 310–311: independent laws for the
    function and tangent-derivative oscillation suprema η and ζ. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP PartialFunctionUP RelativeDifferential
  ExtendedSupremumUP RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_function_oscillation_values]: zero and the
    quotients defining η in 3.4.2(4), pp. 310–311. The pairs retain the
    original S and C, x-c in Z, and 0<|x-c|<=delta. *)
Definition critical_function_oscillation_values (R:realType) m (Y:lmodType R)
    (NY:Y->R) (Z:subspace (R_n R m)) (S C:set (R_n R m))
    (f:R_n R m->Y) (lambda delta:R):set R:=
  [set q|q=0 \/exists x c,S x /\C c /\Z (x-c) /\
    0<inner_norm (@euclidean_inner_productP R m) (x-c)<=delta /\
    q=NY (f x-f c)/real_power
      (inner_norm (@euclidean_inner_productP R m) (x-c)) lambda].

(** Source for [is_critical_function_oscillation]: η is the extended
    supremum of the printed real quotients, 3.4.2(4), pp. 310–311.
    Infinite suprema remain possible. The book uses lambda>=0 and
    delta>0; nonpositive cutoffs have only the adjoined zero value. *)
Definition is_critical_function_oscillation (R:realType) m (Y:lmodType R)
    (NY:Y->R) (Z:subspace (R_n R m)) (S C:set (R_n R m))
    (f:R_n R m->Y) (lambda delta:R) (v: \bar R):Prop:=
  is_extended_supremum (critical_function_oscillation_values NY Z S C f lambda delta) v.

(** Source for [critical_tangent_oscillation_values]: zero and the
    quotients defining ζ in 3.4.2(4), p. 311. The two differential graphs
    require the genuine relative derivative at x and its value on z.
    Its exact tangent domain ensures z belongs to Tan(S,x); the other
    tests retain z in Z, |z|<=1, and the printed source pairs. *)
Definition critical_tangent_oscillation_values (R:realType) m (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (Z:subspace (R_n R m))
    (S C:set (R_n R m)) (f:R_n R m->Y) (lambda delta:R):set R:=
  [set q|q=0 \/exists x c z (D:partial_function (R_n R m) Y) y,
    S x /\C c /\Z (x-c) /\
    0<inner_norm (@euclidean_inner_productP R m) (x-c)<=delta /\
    Z z /\inner_norm (@euclidean_inner_productP R m) z<=1 /\
    partial_function_graph (relative_norm_differential
      (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY S S f) x D /\
    partial_function_graph D z y /\
    q=NY y/real_power (inner_norm (@euclidean_inner_productP R m) (x-c)) lambda].

(** Source for [is_critical_tangent_oscillation]: ζ is the extended
    supremum of the derivative quotients in 3.4.2(4), p. 311. On class-one
    maps this uses every original tangent test. It assigns no derivative
    value outside the relative differential's domain. *)
Definition is_critical_tangent_oscillation (R:realType) m (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (Z:subspace (R_n R m))
    (S C:set (R_n R m)) (f:R_n R m->Y) (lambda delta:R) (v: \bar R):Prop:=
  is_extended_supremum (critical_tangent_oscillation_values hNY Z S C f lambda delta) v.
