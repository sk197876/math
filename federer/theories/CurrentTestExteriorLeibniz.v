(** Federer (1969), 4.1.7, p. 356: the
    original graded exterior product identity on
    actual compact tests. Exact equal-degree
    transports retain every original degree. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms Alternating AlternatingSum
  AlternatingProduct ScalarCoefficients ExteriorHomogeneousProducts ComassWedgeSymmetry CurrentSpaces
  SmoothTestSpaces SmoothTestEvaluation CurrentTestValueLaws CurrentDegreeTransport
  SmoothCurrentFormProduct SmoothCurrentExteriorDerivative SmoothCurrentExteriorLeibniz
  CurrentTestExteriorDerivative CurrentTestFormProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentTestExteriorLeibniz.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation hE := (fun m=>@current_smooth_space_laws R h2 n U hU m).
Local Notation ev := (fun m=>@current_test_value R h2 n U hU m).
Local Notation sv := (fun m=>@current_smooth_value R h2 n U hU m).
Local Notation inc := (fun m=>smooth_test_inclusion (hE m)).
Local Notation sd := (fun m=>@smooth_current_exterior_derivative R h2 n m U hU).
Local Notation d := (fun m=>@current_test_exterior_derivative R h2 n m U hU).
Local Notation P := (fun a b=>@current_test_form_product R h2 n a b U hU).
Local Notation Tr := (fun m q (h:m=q)=>@current_test_degree_transport R h2 n U hU m q h).

(** Source for [current_test_exterior_leibniz]: the
    exact original graded product rule on tests,
    supporting the boundary–contraction equation of
    Federer 4.1.7, p. 356. *)
Theorem current_test_exterior_leibniz phi psi:
  d (k+p) (P k p phi psi)=
    Tr _ _ (addSn k p) (P k.+1 p (sd k phi) psi)+
      (-1:R)^+k*:Tr _ _ (addnS k p) (P k p.+1 phi (d p psi)).
Proof.
apply:(smooth_test_values_extensional (hE (k+p).+1))=>x hx.
change (ev (k+p).+1 (d (k+p) (P k p phi psi)) x=
  ev (k+p).+1 (Tr _ _ (addSn k p) (P k.+1 p (sd k phi) psi)+
    (-1:R)^+k*:Tr _ _ (addnS k p) (P k p.+1 phi (d p psi))) x).
change (smooth_test_values_hom (hE (k+p).+1) (d (k+p) (P k p phi psi)) x=
  smooth_test_values_hom (hE (k+p).+1)
    (Tr _ _ (addSn k p) (P k.+1 p (sd k phi) psi)+
      (-1:R)^+k*:Tr _ _ (addnS k p) (P k p.+1 phi (d p psi))) x).
rewrite linearD linearZ.
change (ev (k+p).+1 (d (k+p) (P k p phi psi)) x=
  ev (k+p).+1 (Tr _ _ (addSn k p) (P k.+1 p (sd k phi) psi)) x+
    (-1:R)^+k*:ev (k+p).+1 (Tr _ _ (addnS k p) (P k p.+1 phi (d p psi))) x).
have hA:=@current_test_degree_transport_values R h2 n U hU _ _ (addSn k p)
  (P k.+1 p (sd k phi) psi) x.
have hB:=@current_test_degree_transport_values R h2 n U hU _ _ (addnS k p)
  (P k p.+1 phi (d p psi)) x.
rewrite hA hB.
apply:(can_inj (@form_includeK R X R^o (k+p).+1)).
rewrite linearD linearZ.
change (form_include (ev (k+p).+1 (d (k+p) (P k p phi psi)) x)=
  form_include (form_reindex (addSn k p) (ev (k.+1+p) (P k.+1 p (sd k phi) psi) x))+
    (-1:R)^+k*:form_include (form_reindex (addnS k p) (ev (k+p.+1) (P k p.+1 phi (d p psi)) x))).
rewrite !form_reindex_include.
have hLeft:ev (k+p).+1 (d (k+p) (P k p phi psi)) x=
    sv (k+p).+1 (sd (k+p) (@smooth_current_form_product R h2 n k p U hU phi (inc p psi))) x.
  change (sv (k+p).+1 (inc (k+p).+1 (d (k+p) (P k p phi psi))) x=
    sv (k+p).+1 (sd (k+p) (@smooth_current_form_product R h2 n k p U hU phi (inc p psi))) x).
  by rewrite (@current_test_exterior_derivative_inclusion R h2 n (k+p) U hU (P k p phi psi))
    (@current_test_form_product_inclusion R h2 n k p U hU phi psi).
rewrite hLeft.
rewrite (@current_test_form_product_values R h2 n k.+1 p U hU (sd k phi) psi x hx)
  (@current_test_form_product_values R h2 n k p.+1 U hU phi (d p psi) x hx).
rewrite !form_wedge_include.
have hDpsi:ev p.+1 (d p psi) x=sv p.+1 (sd p (inc p psi)) x.
  change (sv p.+1 (inc p.+1 (d p psi)) x=sv p.+1 (sd p (inc p psi)) x).
  by rewrite (@current_test_exterior_derivative_inclusion R h2 n p U hU psi).
rewrite hDpsi.
exact:(@smooth_current_exterior_leibniz_values R h2 n k p U hU phi (inc p psi) x hx).
Qed.
End CurrentTestExteriorLeibniz.
