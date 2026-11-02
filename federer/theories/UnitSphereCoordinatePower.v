(** Federer (1969), 3.2.13, p. 251: coordinate
    powers are compact continuous tests on the unit sphere for
    positive exponents, and their actual moments are the Gamma quotient. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal functions
  topology subtype_topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCoordinateTopology UnitSphereSpace UnitSphereIntegralTransfer SphereCoordinateMoment
  SphereCoordinateParameters EulerGamma EulerGammaHalfParameters RealPower RealPowerContinuity
  CompactSupportFunctionUP IsotropyGroupTopology MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [unit_sphere_coordinate_power]: the function
    |u_i|^t on S^(m-1) in Federer 3.2.13, p. 251. *)
Definition unit_sphere_coordinate_power (R:realType) m (i:'I_m) (t:R)
    (u:euclidean_unit_sphere_space R m):R:=real_power `|set_val u i| t.

(** Source for [unit_sphere_coordinate_power_continuous]: the
    positive coordinate-power test is continuous for the Haar
    comparison in Federer 3.2.13, p. 251; the printed moment
    at negative exponents is handled by integration instead. *)
Lemma unit_sphere_coordinate_power_continuous (R:realType) m (i:'I_m) (t:R):
  0<t ->continuous (unit_sphere_coordinate_power i t:
    euclidean_unit_sphere_space R m->real_line_metric R).
Proof.
move=>ht.
have hC:continuous (fun u:euclidean_unit_sphere_space R m=>(set_val u i:R^o)).
  move=>u; exact:continuous_comp
    (@set_type_val_continuous [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
      (@euclidean_unit_sphere_set R m) u) (@euclidean_coordinate_continuous R m i (set_val u)).
have hAbs:continuous (fun u:euclidean_unit_sphere_space R m=>(`|set_val u i| :real_line_metric R)).
  move=>u; exact:cvg_norm (hC u).
exact:(@real_power_continuous_comp R (euclidean_unit_sphere_space R m)
  (fun u=>`|set_val u i|) t hAbs (fun u=>normr_ge0 (set_val u i)) ht).
Qed.

(** Source for [unit_sphere_coordinate_power_compact]: |u_i|^t
    is in K(S^(m-1)) for t>0, supporting the
    invariant-integral uniqueness argument in Federer 3.2.13, p. 251. *)
Lemma unit_sphere_coordinate_power_compact (R:realType) m (i:'I_m) (t:R):
  0<t ->compactly_supported_continuous_functions (unit_sphere_coordinate_power i t).
Proof.
move=>ht; split; first exact:unit_sphere_coordinate_power_continuous ht.
exact:(subclosed_compact (@real_function_support_closed R (euclidean_unit_sphere_space R m) _)
  (@euclidean_unit_sphere_space_compact R m) (@subsetT _ _)).
Qed.

(** Source for [unit_sphere_coordinate_power_integral]: the
    full coordinate moment in the intrinsic sphere measure,
    Federer 3.2.13, p. 251, for all t>-1. *)
Lemma unit_sphere_coordinate_power_integral (R:realType) m (hm:(0<m)%N)
    (i:'I_m) (t:R) (ht:-1<t):
  is_measure_integral (@unit_sphere_hausdorff_measure R m)
    (real_total_integrand (unit_sphere_coordinate_power i t))
    (2*euler_gamma (positive_coordinate_moment_parameter ht)*(euler_gamma_half R)^+(m-1)/
      euler_gamma (@positive_coordinate_moment_denominator R m t hm ht))%:E.
Proof.
exact ((@unit_sphere_intrinsic_integral_iff R m _ _).2
  (@hausdorff_unit_sphere_coordinate_moment R m hm i t ht)).
Qed.
