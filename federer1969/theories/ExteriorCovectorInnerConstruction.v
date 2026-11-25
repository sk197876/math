(** Federer (1969), 1.7.5, p. 33: existence of the inner product on
    m-covectors making gamma_m orthogonal. Private construction: transport
    the already proved inner product along an inverse. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorPositivity
  InnerExteriorIsomorphism ExteriorCovectorInnerUP BilinearPrecompose
  LinearBasis ExteriorGrading AlternatingCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_covector_inner_exists]: Federer
    1.7.5, p. 33, finite dimension makes gamma_m an isomorphism,
    allowing transport of the inner product to the covectors. *)
Theorem exterior_covector_inner_exists (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m :
  exists D : A_m V R^o m -> A_m V R^o m -> R,
    is_exterior_covector_inner_product h2 hB D.
Proof.
have [g [hfg hgf]] := @inner_exterior_inverse_exists R h2 V B hB n e he m.
pose C := @exterior_inner_form R h2 V B hB m.
have hC := @exterior_inner_productP R h2 V B hB m.
exists (fun a b => C (g a) (g b)); constructor.
- constructor.
  + exact (@bilinear_linear_precompose R (A_m V R^o m) (A_m V R^o m)
      (exterior_power V m) (exterior_power V m) R^o C (inner_bilinear hC) g g).
  + move=> a b; exact (@inner_symmetric R (exterior_power V m) C hC (g a) (g b)).
  + move=> a; rewrite (inner_positive hC) -(linear0 g).
    by rewrite (inj_eq (can_inj hgf)).
- move=> x y; by rewrite !hfg.
Qed.
