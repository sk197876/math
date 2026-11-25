(** Federer (1969), 4.1.7, p. 356: the
    original directional product rule on actual
    compact test forms, before transposition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothTestSpaces LinearSubspaceRepresentationUP
  CurrentDirectionalDerivative CurrentTestDirectionalInclusion CurrentTestFormProduct
  SmoothCurrentFormProduct SmoothCurrentFormDirectionalProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentTestFormDirectionalProduct.
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
Local Notation P := (@current_test_form_product R h2 n k p U hU).

(** Source for [current_test_form_product_directional]:
    the original test-form directional Leibniz rule,
    supporting Federer 4.1.7, p. 356. *)
Theorem current_test_form_product_directional phi psi:
  d (k+p) (P phi psi)= P (L k phi) psi+P phi (d p psi).
Proof.
apply:(subspace_representation_injective (smooth_test_space_laws (hE (k+p)))).
change (inc (k+p) (d (k+p) (P phi psi))=
  inc (k+p) (P (L k phi) psi+P phi (d p psi))).
rewrite (@current_test_directional_derivative_inclusion R h2 n (k+p) U hU v (P phi psi)).
rewrite (@current_test_form_product_inclusion R h2 n k p U hU phi psi).
rewrite linearD.
change (L (k+p) (@smooth_current_form_product R h2 n k p U hU phi (inc p psi))=
  inc (k+p) (P (L k phi) psi)+inc (k+p) (P phi (d p psi))).
rewrite (@current_test_form_product_inclusion R h2 n k p U hU (L k phi) psi).
rewrite (@current_test_form_product_inclusion R h2 n k p U hU phi (d p psi)).
rewrite (@current_test_directional_derivative_inclusion R h2 n p U hU v psi).
exact:smooth_current_form_product_directional.
Qed.
End CurrentTestFormDirectionalProduct.
