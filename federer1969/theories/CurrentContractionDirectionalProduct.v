(** Federer (1969), 4.1.7, p. 356: the
    displayed D_j product rule for current contraction.
    It follows by transposing the original test
    product identity, with the original minus sign. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentEvaluation CurrentContraction
  CurrentDirectionalDerivative CurrentTestFormProduct CurrentTestFormDirectionalProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentContractionDirectionalProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable v:X.
Local Notation L := (fun m=>@current_smooth_directional_derivative R h2 n m U hU v).
Local Notation D := (fun m=>@current_directional_derivative R h2 n m U hU v).
Local Notation P := (@current_contraction R h2 n k p U hU).

(** Source for [current_contraction_directional_product]:
    D_j(T contracted phi)=(D_j T) contracted phi
    plus T contracted D_j phi, Federer 4.1.7,
    p. 356. The theorem holds in every fixed
    direction, hence in each original coordinate. *)
Theorem current_contraction_directional_product T phi:
  D p (P phi T)= P phi (D (k+p) T)+P (L k phi) T.
Proof.
apply:(@current_values_extensional R h2 n p U hU)=>psi.
rewrite current_directional_derivative_evaluation current_contraction_evaluation.
rewrite linearD !hom_addE !current_contraction_evaluation current_directional_derivative_evaluation.
rewrite current_test_form_product_directional linearD.
by rewrite opprD addrAC addNr add0r.
Qed.
End CurrentContractionDirectionalProduct.
