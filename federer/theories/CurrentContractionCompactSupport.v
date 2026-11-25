(** Federer (1969), 4.1.7, p. 358: a
    compact test multiplier gives a compactly
    supported current. The proof uses the
    original support-annihilation criterion and the
    actual pointwise exterior product. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingProduct ScalarCoefficients
  CurrentCoefficientNorms CurrentSpaces CurrentContraction CurrentTestFormProduct CurrentTestValueLaws
  CurrentSupportGeometry SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentContractionCompactSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (fun m=>A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (fun m=>@current_form_comass R h2 n m).
Local Notation hNY := (fun m=>@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E := (fun m=>@current_smooth_space R h2 n U hU m).
Local Notation ev := (fun m=>@current_smooth_value R h2 n U hU m).
Local Notation hE := (fun m=>@current_smooth_space_laws R h2 n U hU m).
Local Notation DT := (fun m=>@current_test_space R h2 n U hU m).
Local Notation value := (fun m=>@current_test_value R h2 n U hU m).
Local Notation C := (fun m=>@current_space R h2 n U hU m).
Local Notation action := (fun m=>@current_value R h2 n U hU m).
Local Notation P := (@current_test_form_product R h2 n k p U hU).
Local Notation CP := (@current_contraction R h2 n k p U hU).

(** Source for [current_contraction_support_compact_bound]:
    contraction by a smooth form supported
    in K gives a current supported in K,
    supporting the normality criterion in
    Federer 4.1.7, p. 358. *)
Theorem current_contraction_support_compact_bound (K:smooth_compact_set hNX U) (phi:E k) (T:C (k+p)):
  @smooth_function_support R X (Y k) NX hNX U (E k) (ev k) phi `<=` smooth_compact_carrier K->
  @current_support R h2 n U hU p (CP phi T) `<=` smooth_compact_carrier K.
Proof.
move=>hPhi;apply:(@current_support_compact_criterion R h2 n p U hU K (CP phi T)).2=>psi hPsi.
have hPhiZero:=(@smooth_function_compact_support_iff R X (Y k) NX (NY k) hNX (hNY k)
  U (E k) (ev k) (hE k) K phi).1 hPhi.
have hProduct:P phi psi=0.
  apply:(smooth_test_values_extensional (hE (k+p)))=>x hx.
  change (value (k+p) (P phi psi) x=value (k+p) (0:DT (k+p)) x).
  have hValue:value (k+p) (P phi psi) x=
      form_wedge h2 (scalar_bilinear R) (ev k phi x) (value p psi x).
    exact:(@current_test_form_product_values R h2 n k p U hU phi psi x hx).
  have hZero:value (k+p) (0:DT (k+p)) x=0:=
    @current_test_zero_value R h2 n (k+p) U hU x.
  apply:(eq_trans hValue).
  apply:(eq_trans _ (esym hZero)).
  case:(pselect (smooth_compact_carrier K x))=>hKx.
  - have hPsiZero:value p psi x=0.
      apply:contrapT=>hNo.
      have hSupport:=@smooth_function_nonzero_in_support R X (Y p) NX hNX U (DT p)
        (value p) psi x hx hNo.
      exact:(hPsi x hSupport).2 hKx.
    by rewrite hPsiZero (bil0r (@form_wedge_bilinear R h2 X R^o _ (scalar_bilinear R) k p)).
  - by rewrite (@hPhiZero x hKx)
      (bil0l (@form_wedge_bilinear R h2 X R^o _ (scalar_bilinear R) k p)).
by rewrite current_contraction_evaluation hProduct linear0.
Qed.

(** Source for [current_contraction_by_test_compact]:
    every original compact test multiplier gives
    compact support, supporting T contracted gamma
    in Federer 4.1.7, p. 358. *)
Theorem current_contraction_by_test_compact (gamma:DT k) (T:C (k+p)):
  compact [set x:real_norm_metric_space hNX|
    @current_support R h2 n U hU p (CP (smooth_test_inclusion (hE k) gamma) T) x].
Proof.
have[K hK]:=smooth_test_support_bound (hE k) gamma.
apply:(@current_support_compact_bound R h2 n p U hU K
  (CP (smooth_test_inclusion (hE k) gamma) T)).
exact:(@current_contraction_support_compact_bound K (smooth_test_inclusion (hE k) gamma) T hK).
Qed.
End CurrentContractionCompactSupport.
