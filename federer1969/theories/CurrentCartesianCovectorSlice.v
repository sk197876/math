(** Federer (1969), 4.1.8, p. 360: the original
    slice of a separated covector product has its diagonal
    pairing value and vanishes in every off-diagonal mixed
    degree. The proof reuses the original direct-sum exterior
    inverse and covector-product laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import BoundedHom HomogeneousHom GradedComponents Hom AlgebraUP TensorUP Bilinear
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockLinearMaps
  ExteriorAlgebra ExteriorGrading ExteriorMaps ExteriorHomogeneousProducts
  AlternatingForms AlternatingExtension AlternatingSum AlternatingPairing AlternatingDual
  AlternatingProduct ScalarCoefficients ComassWedgeSymmetry CurrentVectorFormInterior
  CurrentInteriorPairing CovectorBlockProductPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianCovectorSlice.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation p := (hom_as_linear (@euclidean_first_block_map R m n)).
Local Notation q := (hom_as_linear (@euclidean_last_block_map R m n)).
Local Notation P := (hom_as_linear (@euclidean_first_injection_map R m n)).
Local Notation Q := (hom_as_linear (@euclidean_last_injection_map R m n)).

(** Source for [current_cartesian_covector_slice_pairing]: the
    defining slice pairing of a separated covector product,
    supporting Federer 4.1.8, p. 360. The factors
    may have any mixed degrees with the original total;
    only equal-degree identifications are used. *)
Theorem current_cartesian_covector_slice_pairing i j k l (e:(k+l)%N=(i+j)%N)
    (alpha:A_m X R^o k) (beta:A_m Y R^o l)
    (xi:exterior_power X i) (eta:exterior_power Y j):
  pairing xi (A_m_dual P
    (@current_vector_form_interior R Z j i (exterior_power_map Q j eta)
      (form_reindex (addnC i j) (form_reindex e
        (form_wedge h2 (scalar_bilinear R) (A_m_dual p alpha) (A_m_dual q beta))))))=
    form_include alpha (component_val xi)*form_include beta (component_val eta).
Proof.
rewrite A_m_dual_pairing.
change (form_include
  (@current_vector_form_interior R Z j i (exterior_power_map Q j eta)
    (form_reindex (addnC i j) (form_reindex e
      (form_wedge h2 (scalar_bilinear R) (A_m_dual p alpha) (A_m_dual q beta)))))
    (component_val (exterior_power_map P i xi))=
  form_include alpha (component_val xi)*form_include beta (component_val eta)).
rewrite current_vector_form_interior_include !form_reindex_include.
change (form_include (form_wedge h2 (scalar_bilinear R) (A_m_dual p alpha) (A_m_dual q beta))
  (wedge (exterior_algebra_map P (component_val xi))
    (exterior_algebra_map Q (component_val eta)))=
  form_include alpha (component_val xi)*form_include beta (component_val eta)).
exact:(@covector_block_product_factorisation R h2 Z X Y p q P Q
  (@euclidean_first_block_injectionK R m n) (@euclidean_last_block_injectionK R m n)
  (fun z=>esym (@euclidean_block_linear_decomposition R m n z)) i j k l alpha beta xi eta).
Qed.

(** Source for [current_cartesian_covector_slice_diagonal]: the
    original diagonal separated slice is alpha multiplied by
    the scalar pairing with beta, supporting Federer 4.1.8,
    p. 360. Both zero degrees are included. *)
Theorem current_cartesian_covector_slice_diagonal i j
    (alpha:A_m X R^o i) (beta:A_m Y R^o j) (eta:exterior_power Y j):
  A_m_dual P (@current_vector_form_interior R Z j i (exterior_power_map Q j eta)
    (form_reindex (addnC i j)
      (form_wedge h2 (scalar_bilinear R) (A_m_dual p alpha) (A_m_dual q beta))))=
    pairing eta beta*:alpha.
Proof.
apply:pairing_ext=>xi.
have hPair:=@current_cartesian_covector_slice_pairing i j i j erefl alpha beta xi eta.
change (pairing xi (A_m_dual P
  (@current_vector_form_interior R Z j i (exterior_power_map Q j eta)
    (form_reindex (addnC i j) (form_wedge h2 (scalar_bilinear R)
      (A_m_dual p alpha) (A_m_dual q beta)))))=
  pairing xi (pairing eta beta*:alpha)).
rewrite (bilZr (@pairing_bilinear R X R^o i)).
change (pairing xi (A_m_dual P
  (@current_vector_form_interior R Z j i (exterior_power_map Q j eta)
    (form_reindex (addnC i j) (form_wedge h2 (scalar_bilinear R)
      (A_m_dual p alpha) (A_m_dual q beta)))))=
  pairing eta beta*pairing xi alpha).
exact:(eq_trans hPair (mulrC _ _)).
Qed.

(** Source for [current_cartesian_covector_slice_off_diagonal]:
    every separated mixed degree with k different from i
    has zero original slice, supporting Federer 4.1.8,
    p. 360. No simplicity or positivity hypothesis is
    imposed on either factor. *)
Theorem current_cartesian_covector_slice_off_diagonal i j k l (e:(k+l)%N=(i+j)%N)
    (alpha:A_m X R^o k) (beta:A_m Y R^o l) (eta:exterior_power Y j):
  k<>i->A_m_dual P
    (@current_vector_form_interior R Z j i (exterior_power_map Q j eta)
      (form_reindex (addnC i j) (form_reindex e
        (form_wedge h2 (scalar_bilinear R) (A_m_dual p alpha) (A_m_dual q beta)))))=0.
Proof.
move=>hDifferent;apply:pairing_ext=>xi.
rewrite (@current_cartesian_covector_slice_pairing i j k l e alpha beta xi eta).
have hDegree:i!=k by apply/eqP=>he;apply:hDifferent;exact:esym he.
have hZero:=hom_m_degree (form_homogeneous alpha) hDegree (component_homogeneous xi).
change (form_homogeneous alpha (component_val xi)=0) in hZero.
change (form_homogeneous alpha (component_val xi)*form_include beta (component_val eta)=pairing xi 0).
by rewrite hZero mul0r (bil0r (@pairing_bilinear R X R^o i)).
Qed.
End CurrentCartesianCovectorSlice.
