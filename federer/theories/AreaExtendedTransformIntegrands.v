(** Federer (1969), 3.2.20, pp. 256–257: supporting
    extended-real-weight versions of the two integrands in 3.2.5,
    p. 244, used on each compact parameter chart. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations ExtendedRealOrderTopology PartialFunctionBasic PartialZeroExtension
  PartialDensityProduct EuclideanJacobianMeasurable MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [area_extended_source_integrand]: supporting left
    integrand in the two applications of 3.2.5(2) in Federer
    3.2.20, p. 257. The weight may be extended-real;
    the actual ordinary Jacobian domain remains unchanged on A. *)
Definition area_extended_source_integrand (R : realType) m n
    (f : R_n R m -> R_n R n) (A : set (R_n R m))
    (g : R_n R n -> \bar R) :=
  partial_function_zero_extension (0:extended_real_line R) A
    (partial_density_product (partial_function_total (fun x=>g (f x) : extended_real_line R))
      (extended_euclidean_jacobian f)).

(** Source for [area_extended_target_integrand]: supporting right
    integrand in the two applications of 3.2.5(2) in Federer
    3.2.20, p. 257. Multiplicity counts the original
    source fibre and the distinguished zero-infinity product is retained. *)
Definition area_extended_target_integrand (R : realType) m n
    (f : R_n R m -> R_n R n) (A : set (R_n R m))
    (g : R_n R n -> \bar R) :=
  partial_function_total (fun y=>g y* @mapping_multiplicity R _ _ f A y : extended_real_line R).
