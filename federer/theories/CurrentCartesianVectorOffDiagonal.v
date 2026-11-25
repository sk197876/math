(** Federer (1969), 4.1.8, pp. 360–361:
    the original product-density coefficient annihilates
    every off-diagonal separated covector. This is the
    earlier original homogeneous covector law, not a new
    vanishing premise on the currents. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom BoundedHom HomogeneousHom GradedComponents
  GrassmannAbbreviations EuclideanBlockLinearMaps ExteriorGrading ExteriorHomogeneousProducts
  AlternatingForms AlternatingExtension AlternatingSum AlternatingDual AlternatingProduct
  AlternatingPairing ScalarCoefficients ComassWedgeSymmetry
  CurrentCartesianVectorProduct CurrentCartesianVectorPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianVectorOffDiagonal.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).
Local Notation F := (@current_cartesian_vector_product R m n i j).

(** Source for [current_cartesian_vector_off_diagonal]:
    the full original off-diagonal separated pairing is
    zero, supporting Federer 4.1.8, pp. 360–361.
    The equality identifies only equal total degrees. *)
Theorem current_cartesian_vector_off_diagonal k l (e:(k+l)%N=(i+j)%N)
    (xi:exterior_power X i) (eta:exterior_power Y j)
    (a:A_m X R^o k) (b:A_m Y R^o l):k<>i ->
  pairing (F xi eta) (form_reindex e (form_wedge h2 (scalar_bilinear R)
    (A_m_dual (hom_as_linear p) a) (A_m_dual (hom_as_linear q) b)))=0.
Proof.
move=>hki.
change (form_include (form_reindex e (form_wedge h2 (scalar_bilinear R)
    (A_m_dual (hom_as_linear p) a) (A_m_dual (hom_as_linear q) b)))
    (component_val (F xi eta))=0).
rewrite form_reindex_include current_cartesian_vector_pairing_all_degrees.
have hDegree:(i != k)%N by apply/eqP=>hik;apply:hki;exact:esym hik.
have hZero:form_include a (component_val xi)=0.
  change (form_extension a (component_val xi)=0).
  exact:(@form_extension_degree R X R^o k a i (component_val xi) hDegree (component_homogeneous xi)).
by rewrite hZero mul0r.
Qed.
End CurrentCartesianVectorOffDiagonal.
