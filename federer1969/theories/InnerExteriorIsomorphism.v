(** Federer (1969), 1.7.5, p. 33: gamma_m is an isomorphism in finite
    dimension. The inverse is obtained from the abstract basis
    correspondence, not by inspecting gamma. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity InnerExterior InnerExteriorBasis
  InnerExteriorPositivity InnerExteriorPolarity OrthogonalMaps
  LinearBasis IndependentMap FiniteExteriorPowers ExteriorIndices ExteriorGrading
  AlternatingCoordinates CovectorProducts GrassmannCoordinates
  OrthonormalFamilies GramSchmidt OrthonormalisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [inner_exterior_inverse_orthonormal_basis]:
    Federer 1.7.5, p. 33, gamma_m sends the orthonormal
    exterior basis to the dual covector-product basis, so has a
    two-sided linear inverse. *)
Theorem inner_exterior_inverse_orthonormal_basis (R : realFieldType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (ho : orthonormal_family B e) m :
  exists g : {linear A_m V R^o m -> exterior_power V m},
    cancel (@inner_exterior_form R h2 V B hB m) g /\
    cancel g (@inner_exterior_form R h2 V B hB m).
Proof.
pose omega i := inner_polarity hB (e i).
have hd i j : omega i [tuple e j] = if i==j then 1 else 0.
  by rewrite /omega inner_polarityE ho eq_sym.
have hb := @finite_e_lambda_basis R n V e he h2 m.
have hw := @omega_lambda_basis R h2 V n m e omega he hd.
have hg : is_basis (fun lambda : Lambda n m =>
    inner_exterior_form h2 hB (e_lambda e (val lambda))).
  apply: basis_congr hw => lambda.
  by rewrite inner_exterior_basis_covectors.
exact: (@basis_image_inverse_exists R (Choice.clone (Lambda n m) _)
  (exterior_power V m) (A_m V R^o m) (fun lambda => e_lambda e (val lambda)) hb
  (GRing.Linear.clone _ _ _ _ (@inner_exterior_form R h2 V B hB m) _) hg).
Qed.

(** Source for [inner_exterior_inverse_exists]: Federer
    1.7.5, p. 33, gamma_m is a linear isomorphism for every
    finite-dimensional inner-product space and every degree. *)
Theorem inner_exterior_inverse_exists (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m :
  exists g : {linear A_m V R^o m -> exterior_power V m},
    cancel (@inner_exterior_form R h2 V B hB m) g /\
    cancel g (@inner_exterior_form R h2 V B hB m).
Proof.
have [d [hd hdo]] := @orthonormal_basis_exists R V B hB n e he.
exact: (@inner_exterior_inverse_orthonormal_basis R h2 V B hB n d hd
  (orthonormalisation_orthonormal hdo) m).
Qed.
