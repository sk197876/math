(** Federer (1969), 4.1.7, p. 356: the
    original vector directional product rule on actual
    compact test forms, before transposition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothTestSpaces LinearSubspaceRepresentationUP
  CurrentDirectionalDerivative CurrentVectorDirectionalDerivative CurrentTestDirectionalInclusion CurrentTestVectorInterior
  SmoothCurrentVectorInterior SmoothCurrentVectorDirectionalProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentTestVectorDirectionalProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation hE := (fun m=>@current_smooth_space_laws R h2 n U hU m).
Local Notation inc := (fun m=>smooth_test_inclusion (hE m)).
Variable v:X.
Local Notation L := (fun m=>@current_smooth_directional_derivative R h2 n m U hU v).
Local Notation d := (fun m=>@current_test_directional_derivative R h2 n m U hU v).
Local Notation VL := (fun m=>@current_vector_smooth_directional_derivative R h2 n m U hU v).
Local Notation P := (@current_test_vector_interior R h2 n k p U hU).

(** Source for [current_test_vector_interior_directional]:
    the original vector-interior directional Leibniz rule,
    supporting Federer 4.1.7, p. 356. *)
Theorem current_test_vector_interior_directional xi psi:
  d p (P xi psi)= P (VL k xi) psi+P xi (d (k+p) psi).
Proof.
apply:(subspace_representation_injective (smooth_test_space_laws (hE p))).
change (inc p (d p (P xi psi))=
  inc p (P (VL k xi) psi+P xi (d (k+p) psi))).
rewrite (@current_test_directional_derivative_inclusion R h2 n p U hU v (P xi psi)).
rewrite (@current_test_vector_interior_inclusion R h2 n k p U hU xi psi).
rewrite linearD.
change (L p (@smooth_current_vector_interior R h2 n k p U hU xi (inc (k+p) psi))=
  inc p (P (VL k xi) psi)+inc p (P xi (d (k+p) psi))).
rewrite (@current_test_vector_interior_inclusion R h2 n k p U hU (VL k xi) psi).
rewrite (@current_test_vector_interior_inclusion R h2 n k p U hU xi (d (k+p) psi)).
rewrite (@current_test_directional_derivative_inclusion R h2 n (k+p) U hU v psi).
exact:smooth_current_vector_interior_directional.
Qed.
End CurrentTestVectorDirectionalProduct.
