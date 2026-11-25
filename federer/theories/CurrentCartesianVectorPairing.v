(** Federer (1969), 4.1.8, pp. 360–361: the
    original product-density coefficient has the original
    separated-test pairings in every mixed degree. Reuse
    the proved direct-sum factorisation and covector grading. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom BoundedHom HomogeneousHom GradedComponents AlgebraUP
  GrassmannAbbreviations EuclideanBlockLinearMaps ExteriorAlgebra ExteriorGrading ExteriorMaps
  ExteriorHomogeneousProducts AlternatingForms AlternatingExtension AlternatingSum
  AlternatingDual AlternatingProduct AlternatingPairing ScalarCoefficients
  CovectorBlockProductPairing CurrentCartesianVectorProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianVectorPairing.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).
Local Notation P := (@euclidean_first_injection_map R m n).
Local Notation Q := (@euclidean_last_injection_map R m n).
Local Notation F := (@current_cartesian_vector_product R m n i j).

(** Source for [current_cartesian_vector_pairing_all_degrees]:
    the original block product pairs as the two factor
    pairings, supporting Federer 4.1.8, pp. 360–361.
    The homogeneous covectors may have any degrees. *)
Theorem current_cartesian_vector_pairing_all_degrees k l
    (xi:exterior_power X i) (eta:exterior_power Y j)
    (a:A_m X R^o k) (b:A_m Y R^o l):
  form_include (form_wedge h2 (scalar_bilinear R)
    (A_m_dual (hom_as_linear p) a) (A_m_dual (hom_as_linear q) b))
    (component_val (F xi eta))=
    form_include a (component_val xi)*form_include b (component_val eta).
Proof.
change (form_include (form_wedge h2 (scalar_bilinear R)
    (A_m_dual (hom_as_linear p) a) (A_m_dual (hom_as_linear q) b))
    (wedge (exterior_algebra_map (hom_as_linear P) (component_val xi))
      (exterior_algebra_map (hom_as_linear Q) (component_val eta)))=
    form_include a (component_val xi)*form_include b (component_val eta)).
exact:(@covector_block_product_factorisation R h2 Z X Y
  (hom_as_linear p) (hom_as_linear q) (hom_as_linear P) (hom_as_linear Q)
  (@euclidean_first_block_injectionK R m n) (@euclidean_last_block_injectionK R m n)
  (fun z=>esym (@euclidean_block_linear_decomposition R m n z)) i j k l a b xi eta).
Qed.

(** Source for [current_cartesian_vector_pairing]: the
    original diagonal separated pairing of the displayed
    product density, supporting Federer 4.1.8, p. 361. *)
Theorem current_cartesian_vector_pairing
    (xi:exterior_power X i) (eta:exterior_power Y j)
    (a:A_m X R^o i) (b:A_m Y R^o j):
  pairing (F xi eta) (form_wedge h2 (scalar_bilinear R)
    (A_m_dual (hom_as_linear p) a) (A_m_dual (hom_as_linear q) b))=
    pairing xi a*pairing eta b.
Proof. exact:current_cartesian_vector_pairing_all_degrees. Qed.
End CurrentCartesianVectorPairing.
