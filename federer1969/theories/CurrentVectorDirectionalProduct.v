(** Federer (1969), 4.1.7, p. 356: the
    displayed D_j product rule for vector multiplication.
    It follows by transposing the original test
    product identity, with the original minus sign. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentEvaluation CurrentVectorProduct
  CurrentDirectionalDerivative CurrentVectorDirectionalDerivative CurrentTestVectorInterior CurrentTestVectorDirectionalProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentVectorDirectionalProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable v:X.
Local Notation L := (fun m=>@current_vector_smooth_directional_derivative R h2 n m U hU v).
Local Notation D := (fun m=>@current_directional_derivative R h2 n m U hU v).
Local Notation P := (@current_vector_product R h2 n k p U hU).

(** Source for [current_vector_directional_product]:
    D_j(T wedge xi)=(D_j T) wedge xi
    plus T wedge D_j xi, Federer 4.1.7,
    p. 356. The theorem holds in every fixed
    direction, hence in each original coordinate. *)
Theorem current_vector_directional_product T xi:
  D (k+p) (P xi T)= P xi (D p T)+P (L k xi) T.
Proof.
apply:(@current_values_extensional R h2 n (k+p) U hU)=>psi.
rewrite current_directional_derivative_evaluation current_vector_product_evaluation.
rewrite linearD !hom_addE !current_vector_product_evaluation current_directional_derivative_evaluation.
rewrite current_test_vector_interior_directional linearD.
by rewrite opprD addrAC addNr add0r.
Qed.
End CurrentVectorDirectionalProduct.
