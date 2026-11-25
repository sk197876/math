(** Federer (1969), 4.1.19, p. 377: the
    actual coboundary is represented by psi and zero
    on the original U. Both q maps are the
    preceding opaque maps, and the weak equation
    follows from the actual representation. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain FlatCochainSpace FlatCochainCoboundary
  CurrentLonePairFlatSealed FlatCochainRepresentationUP
  FlatCochainCoboundaryRepresentation FlatCochainFormWeakEquation
  CurrentWeakExteriorPairUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [flat_cochain_original_coboundary_representation]:
    the final assertion d alpha=(psi,0) of
    Federer 4.1.19, p. 377, for every
    original representing pair and every natural degree.
    The output includes its original weak equation. *)
Theorem flat_cochain_original_coboundary_representation
    (R : realType) (h2 : (1+1:R)!=0) n m
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (alpha : @flat_cochain_space R h2 n m U hU)
    (phi : current_domain R n U -> A_m (R_n R n) R^o m)
    (psi : current_domain R n U -> A_m (R_n R n) R^o m.+1) :
  @is_flat_cochain_pair_density R h2 n m U hU
    (@CurrentLonePairFlat.map R h2 n m U hU) alpha phi psi ->
  @is_flat_cochain_pair_density R h2 n m.+1 U hU
    (@CurrentLonePairFlat.map R h2 n m.+1 U hU)
    (@flat_cochain_coboundary R h2 n m U hU alpha)
    psi (fun _ : current_domain R n U => 0) /\
  @is_weak_current_exterior_pair R h2 n m.+1 U hU
    psi (fun _ : current_domain R n U => 0).
Proof.
move=> hDensity.
have hBoundary := @flat_cochain_coboundary_form_density R h2 n m U hU
  (@CurrentLonePairFlat.map R h2 n m U hU)
  (@CurrentLonePairFlat.map R h2 n m.+1 U hU)
  (@CurrentLonePairFlat.laws R h2 n m U hU)
  (@CurrentLonePairFlat.laws R h2 n m.+1 U hU)
  alpha phi psi hDensity.
split; first exact: hBoundary.
exact: (@flat_cochain_form_density_weak_equation R h2 n m.+1 U hU
  (@CurrentLonePairFlat.map R h2 n m.+1 U hU)
  (@CurrentLonePairFlat.laws R h2 n m.+1 U hU)
  (@flat_cochain_coboundary R h2 n m U hU alpha)
  psi (fun _ : current_domain R n U => 0) hBoundary).
Qed.
