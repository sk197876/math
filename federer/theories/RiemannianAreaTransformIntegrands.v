(** Federer (1969), 3.2.5, pp. 244–245, extended
    by 3.2.46, p. 282: the actual two displayed
    weighted area integrands. Exact partial domains and
    the distinguished zero-infinity product are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  RiemannianTensorUP RiemannianMetricCarrier RiemannianMapJacobian
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialDensityProduct MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_area_source_integrand]:
    g(f(x)) J_m f(x) integrated on the original S,
    3.2.5, p. 244, with actual Riemannian Jacobian
    as required by 3.2.46, p. 282. Undefined
    differentials remain absent inside S; zero extension
    supplies precisely the original outside-S convention. *)
Definition riemannian_area_source_integrand (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (S : set (riemannian_metric_space hg))
    (u : riemannian_metric_space hh -> real_line_metric R) :=
  partial_function_zero_extension (0 : extended_real_line R) S
    (partial_density_product (partial_function_total (fun x=>((u (f x))%:E : extended_real_line R)))
      (extended_riemannian_map_jacobian f m)).

(** Source for [riemannian_area_target_integrand]:
    g(y) N(f restricted to S,y), 3.2.5, p. 244,
    with actual original-map counting multiplicity and
    actual Riemannian target measure in 3.2.46, p. 282.
    The zero-infinity convention retains zero weight on
    an infinite fibre without assigning a signed infinity difference. *)
Definition riemannian_area_target_integrand (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (S : set (riemannian_metric_space hg))
    (u : riemannian_metric_space hh -> real_line_metric R) :=
  partial_function_total (fun y=>((u y)%:E*@mapping_multiplicity R _ _ f S y : extended_real_line R)).
