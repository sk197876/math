(** Federer (1969), 3.2.5, pp. 244–245: the two
    displayed integral expressions. Use the existing opaque
    zero extension for the source subset and the distinguished
    zero-infinity product for the target multiplicity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations ExtendedRealOrderTopology PartialFunctionBasic PartialZeroExtension
  PartialDensityProduct EuclideanJacobianMeasurable MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [area_transform_source_integrand]: the left
    integrand over A in Federer 3.2.5, p. 244,
    expressed through the subset zero-extension convention
    of 2.4.10. The actual Jacobian domain is retained on A. *)
Definition area_transform_source_integrand (R:realType) m n
    (f:R_n R m->R_n R n) (A:set (R_n R m)) (g:R_n R n->R):=
  partial_function_zero_extension (0:extended_real_line R) A
    (partial_density_product
      (partial_function_total (fun x=>(g (f x))%:E:extended_real_line R))
      (extended_euclidean_jacobian f)).

(** Source for [area_transform_target_integrand]: the right
    integrand g(y) N(f restricted to A,y) in Federer
    3.2.5, p. 244. The finite weight may vanish
    when multiplicity is infinite; the distinguished product
    assigns zero to this pair, as in 2.1.1 and 2.4.10. *)
Definition area_transform_target_integrand (R:realType) m n
    (f:R_n R m->R_n R n) (A:set (R_n R m)) (g:R_n R n->R):=
  partial_function_total (fun y=>((g y)%:E*@mapping_multiplicity R _ _ f A y:extended_real_line R)).
