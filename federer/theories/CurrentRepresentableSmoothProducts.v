(** Federer (1969), 4.1.7, pp. 355–358:
    the original smooth contraction and vector
    products preserve representability by integration.
    Apply the finite compact-test gauge criterion
    with the actual bilinear test multipliers;
    no new density construction is needed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingProduct ScalarCoefficients ExteriorGrading
  CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentVectorSpaces
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation CurrentContraction CurrentVectorProduct
  CurrentTestFormProduct CurrentTestVectorInterior CurrentVectorFormInterior CurrentIntegrationCriterion
  NormFiniteBilinearBound SmoothBilinearTransposeFiniteGauge DistributionFiniteVariationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentRepresentableSmoothProducts.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (fun m=>A_m X R^o m).
Local Notation Z := (fun m=>exterior_power X m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (fun m=>@current_form_comass R h2 n m).
Local Notation hNY := (fun m=>@current_form_comass_real_norm R h2 n m).
Local Notation NZ := (fun m=>@current_vector_mass R h2 n m).
Local Notation hNZ := (fun m=>@current_vector_mass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E := (fun m=>@current_smooth_space R h2 n U hU m).
Local Notation ev := (fun m=>@current_smooth_value R h2 n U hU m).
Local Notation hE := (fun m=>@current_smooth_space_laws R h2 n U hU m).
Local Notation V := (fun m=>@current_vector_smooth_space R h2 n U hU m).
Local Notation vv := (fun m=>@current_vector_smooth_value R h2 n U hU m).
Local Notation hV := (fun m=>@current_vector_smooth_space_laws R h2 n U hU m).
Local Notation DT := (fun m=>@current_test_space R h2 n U hU m).
Local Notation values := (fun m=>smooth_test_values_hom (hE m)).
Local Notation C := (fun m=>@current_space R h2 n U hU m).
Local Notation action := (fun m=>@current_value R h2 n U hU m).
Local Notation represented := (fun m=>@is_integration_representable_current R h2 n m U hU).

(** Source for [current_contraction_represented]: the
    original contraction by an arbitrary smooth
    form preserves integral representability, supporting
    Federer 4.1.7, pp. 355–358,
    including the local normality criterion. *)
Theorem current_contraction_represented (phi:E k) (T:C (k+p)):
  represented (k+p) T->represented p (@current_contraction R h2 n k p U hU phi T).
Proof.
move=>hT.
pose B:=@form_wedge R h2 X R^o _ (scalar_bilinear R) k p.
have hB:=@form_wedge_bilinear R h2 X R^o _ (scalar_bilinear R) k p.
have[dk [bk hBk]]:=@current_form_finite_basis R h2 n k.
have[dp [bp hBp]]:=@current_form_finite_basis R h2 n p.
have hBound:=@norm_finite_bilinear_bounded R (Y k) (Y p) (Y (k+p)) (NY k) (NY p) (NY (k+p))
  (hNY k) (hNY p) (hNY (k+p)) dk dp bk bp hBk hBp B hB.
pose P:=@current_test_form_product R h2 n k p U hU phi.
have hAction:action p (@current_contraction R h2 n k p U hU phi T)=hom_comp (action (k+p) T) P.
  apply:hom_ext=>psi;exact:current_contraction_evaluation.
apply:(@current_integration_finite_gauge_criterion R h2 n p U hU
  (@current_contraction R h2 n k p U hU phi T)).1.
change (@is_finite_distribution_variation R (real_norm_metric_space hNX) U (Y p) (NY p) (DT p)
  (values p) (action p (@current_contraction R h2 n k p U hU phi T))).
rewrite hAction.
exact:(@smooth_bilinear_transpose_finite_gauge R X (Y k) (Y p) (Y (k+p))
  NX (NY k) (NY p) (NY (k+p)) hNX (hNY k) (hNY p) (hNY (k+p)) U
  (E k) (ev k) (hE k) phi (DT p) (DT (k+p)) (values p) (values (k+p)) B hBound P
  (fun psi x hx=>@current_test_form_product_values R h2 n k p U hU phi psi x hx)
  (action (k+p) T) ((@current_integration_finite_gauge_criterion R h2 n (k+p) U hU T).2 hT)).
Qed.

(** Source for [current_vector_product_represented]: the
    original product with an arbitrary smooth
    multivector field preserves integral representability,
    supporting Federer 4.1.7, pp. 355–358.
    The original mass/comass dual spaces are used. *)
Theorem current_vector_product_represented (xi:V k) (T:C p):
  represented p T->represented (k+p) (@current_vector_product R h2 n k p U hU xi T).
Proof.
move=>hT.
pose B:=@current_vector_form_interior R X k p.
have hB:=@current_vector_form_interior_bilinear R X k p.
have[dk [bk hBk]]:=@current_vector_finite_basis R h2 n k.
have[dp [bp hBp]]:=@current_form_finite_basis R h2 n (k+p).
have hBound:=@norm_finite_bilinear_bounded R (Z k) (Y (k+p)) (Y p) (NZ k) (NY (k+p)) (NY p)
  (hNZ k) (hNY (k+p)) (hNY p) dk dp bk bp hBk hBp B hB.
pose P:=@current_test_vector_interior R h2 n k p U hU xi.
have hAction:action (k+p) (@current_vector_product R h2 n k p U hU xi T)=hom_comp (action p T) P.
  apply:hom_ext=>psi;exact:current_vector_product_evaluation.
apply:(@current_integration_finite_gauge_criterion R h2 n (k+p) U hU
  (@current_vector_product R h2 n k p U hU xi T)).1.
change (@is_finite_distribution_variation R (real_norm_metric_space hNX) U (Y (k+p)) (NY (k+p)) (DT (k+p))
  (values (k+p)) (action (k+p) (@current_vector_product R h2 n k p U hU xi T))).
rewrite hAction.
exact:(@smooth_bilinear_transpose_finite_gauge R X (Z k) (Y (k+p)) (Y p)
  NX (NZ k) (NY (k+p)) (NY p) hNX (hNZ k) (hNY (k+p)) (hNY p) U
  (V k) (vv k) (hV k) xi (DT (k+p)) (DT p) (values (k+p)) (values p) B hBound P
  (fun psi x hx=>@current_test_vector_interior_values R h2 n k p U hU xi psi x hx)
  (action p T) ((@current_integration_finite_gauge_criterion R h2 n p U hU T).2 hT)).
Qed.
End CurrentRepresentableSmoothProducts.
