(** Federer (1969), 1.7.6, p. 33: finite-dimensional covector spaces in the
    norm identities. This supporting basis fact follows from the gamma
    isomorphism of 1.7.5, p. 33. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorIsomorphism
  ExteriorGrading ExteriorIndices FiniteExteriorPowers AlternatingCoordinates LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [inner_exterior_image_basis]: Federer 1.7.6,
    p. 33, supporting finite-dimensionality for covector operator
    norms. Gamma carries any exterior basis to a covector basis;
    orthonormality is unnecessary for this basis assertion. *)
Theorem inner_exterior_image_basis (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b) m :
  is_basis (fun lambda : Lambda n m => inner_exterior_form h2 hB (e_lambda b (val lambda))).
Proof.
have [g [hfg hgf]] := @inner_exterior_inverse_exists R h2 V B hB n b hb m.
exact (@basis_transport R (Choice.clone (Lambda n m) _)
  (exterior_power V m) (A_m V R^o m) (fun lambda => e_lambda b (val lambda))
  (GRing.Linear.clone _ _ _ _ (@inner_exterior_form R h2 V B hB m) _) g hfg hgf
  (@finite_e_lambda_basis R n V b hb h2 m)).
Qed.
