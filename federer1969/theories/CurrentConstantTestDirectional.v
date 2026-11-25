(** Federer (1969), 4.1.7, p. 356: original
    coordinate coefficients commute with actual test
    directional differentiation, because those smooth
    coefficients have zero derivative. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentSpaces CurrentConstantFields
  CurrentConstantFieldDirectional CurrentDirectionalDerivative CurrentTestFormProduct
  CurrentTestFormDirectionalProduct CurrentFormProductZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentConstantTestDirectional.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable v:X.
Variable a:A_m X R^o k.
Local Notation phi := (@current_constant_form R h2 n U hU k a).
Local Notation P := (@current_test_form_product R h2 n k p U hU phi).
Local Notation d := (fun m=>@current_test_directional_derivative R h2 n m U hU v).

(** Source for [current_constant_test_directional_commute]:
    D_v(a wedge psi)=a wedge D_v psi for
    each original constant covector a, supporting
    the boundary coordinate formula of Federer
    4.1.7, p. 356. *)
Theorem current_constant_test_directional_commute psi:
  d (k+p) (P psi)= P (d p psi).
Proof.
rewrite (@current_test_form_product_directional R h2 n k p U hU v phi psi)
  (@current_constant_form_directional_zero R h2 n k U hU v a)
  (@current_test_form_product_zero_left R h2 n k p U hU psi) add0r.
reflexivity.
Qed.
End CurrentConstantTestDirectional.
