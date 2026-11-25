(** Federer (1969), 4.1.7, pp. 355–358:
    original Radon-density currents on every open U.
    The canonical current is opaque and its public
    laws give the actual original integration
    representation, with all local norm conditions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentSpaces
  MeasureUP RadonMeasureUP CurrentIntegrationCriterion OpenCurrentDensityUP OpenCurrentDensityExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type OpenCurrentDensitySignature.
(** Source for [value]: original gamma wedge xi
    on the original open U, supporting Federer
    4.1.7, pp. 355–358. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (n m:nat) (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (gamma:set (current_domain R n U)->\bar R) (hGamma:is_measure gamma)
    (hRadon:is_radon_measure gamma)
    (xi:current_domain R n U->exterior_power (R_n R n) m)
    (hField:@is_locally_integrable_open_current_density R h2 n m U gamma xi),@current_space R h2 n U hU m.
(** Source for [laws]: every original test has its
    actual Radon pairing integral; the current
    representation includes the original weak
    measurability and finite compact mass integrals,
    supporting Federer 4.1.7, pp. 355–358. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n m:nat) (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (gamma:set (current_domain R n U)->\bar R) (hGamma:is_measure gamma)
    (hRadon:is_radon_measure gamma)
    (xi:current_domain R n U->exterior_power (R_n R n) m)
    (hField:@is_locally_integrable_open_current_density R h2 n m U gamma xi),
  @is_current_integration_representation R h2 n m U hU
    (@value R h2 n m U hU gamma hGamma hRadon xi hField) gamma xi.
End OpenCurrentDensitySignature.
Module OpenCurrentDensity:OpenCurrentDensitySignature.
(** Source for [value]: seal the proved original
    density-current witness, supporting Federer
    4.1.7, pp. 355–358. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (n m:nat) (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (gamma:set (current_domain R n U)->\bar R) (hGamma:is_measure gamma)
    (hRadon:is_radon_measure gamma)
    (xi:current_domain R n U->exterior_power (R_n R n) m)
    (hField:@is_locally_integrable_open_current_density R h2 n m U gamma xi):@current_space R h2 n U hU m:=
  projT1 (cid (@open_current_from_density_exists R h2 n m U hU gamma hGamma hRadon xi hField)).
(** Source for [laws]: the opaque current satisfies
    its independent original representation law,
    supporting Federer 4.1.7, pp. 355–358. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (n m:nat) (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (gamma:set (current_domain R n U)->\bar R) (hGamma:is_measure gamma)
    (hRadon:is_radon_measure gamma)
    (xi:current_domain R n U->exterior_power (R_n R n) m)
    (hField:@is_locally_integrable_open_current_density R h2 n m U gamma xi):
  @is_current_integration_representation R h2 n m U hU
    (@value R h2 n m U hU gamma hGamma hRadon xi hField) gamma xi.
Proof. exact:(projT2 (cid (@open_current_from_density_exists R h2 n m U hU gamma hGamma hRadon xi hField))). Qed.
End OpenCurrentDensity.
