(** Federer (1969), 4.1.8, p. 360: separated
    constant covectors span the product coefficient space.
    This supporting identity transports the original direct-sum
    exterior product through Omega from 1.4.4, pp. 19–20. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import BoundedHom HomogeneousHom GradedComponents Hom AlgebraUP Tensor TensorMaps
  ExteriorAlgebra ExteriorGrading ExteriorMaps ExteriorDirectSum ExteriorHomogeneousProducts
  AlternatingForms AlternatingSum AlternatingDual AlternatingProduct AlternatingUnit
  ScalarCoefficients OmegaConstruction OmegaNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CovectorBlockTensorImage.
Variable K:fieldType.
Hypothesis h2:(1+1:K)!=0.
Variables V X Y:lmodType K.
Variables (p:{linear V->X}) (q:{linear V->Y}).
Local Notation pDual := (GRing.Linear.clone _ _ _ _ (@Hom_dual K V X (scalar_algebra K) p) _).
Local Notation qDual := (GRing.Linear.clone _ _ _ _ (@Hom_dual K V Y (scalar_algebra K) q) _).

(** Source for [covector_block_tensor_image]: Omega takes
    a pure tensor through the original block exterior map
    to the original pulled-back covector product, supporting
    Federer 4.1.8, p. 360, by 1.3.2 and 1.4.4.
    No finite-dimensional hypothesis is needed for this identity. *)
Theorem covector_block_tensor_image k l
    (xi:exterior_power (Hom X K^o) k) (eta:exterior_power (Hom Y K^o) l):
  Omega h2 V (@ExteriorDirectSum.beta K (Hom V K^o) (Hom X K^o) (Hom Y K^o)
    pDual qDual (tensor_inj (component_val xi) (component_val eta)))=
  form_include (form_wedge h2 (scalar_bilinear K)
    (A_m_dual p (Omega_m h2 xi)) (A_m_dual q (Omega_m h2 eta))).
Proof.
rewrite betaE.
change (@Omega_W K h2 V (scalar_algebra K) (@mulrC K)
  (wedge (exterior_algebra_map pDual (component_val xi))
    (exterior_algebra_map qDual (component_val eta)))=
  form_include (form_wedge h2 (scalar_bilinear K)
    (A_m_dual p (Omega_m h2 xi)) (A_m_dual q (Omega_m h2 eta)))).
rewrite Omega_W_wedge
  -(@Omega_W_natural K h2 V X (scalar_algebra K) p (@mulrC K) (component_val xi))
  -(@Omega_W_natural K h2 V Y (scalar_algebra K) q (@mulrC K) (component_val eta)).
change (alternating_wedge h2 (scalar_bilinear K)
  (A_star_dual p (Omega h2 X (component_val xi)))
  (A_star_dual q (Omega h2 Y (component_val eta)))=
  form_include (form_wedge h2 (scalar_bilinear K)
    (A_m_dual p (Omega_m h2 xi)) (A_m_dual q (Omega_m h2 eta)))).
by rewrite -!Omega_m_include !A_star_dual_include -form_wedge_include.
Qed.
End CovectorBlockTensorImage.
