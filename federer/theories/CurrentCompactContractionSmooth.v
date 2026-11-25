(** Federer (1969), 4.1.20, p. 378: the scalar
    contractions of a compact current are evaluated on the
    smooth coordinate forms. Transpose the original smooth
    product of 4.1.6, p. 353, and use the unique smooth-dual
    extension of 4.1.7, p. 355. No noncompact form is used
    as a test in D'. Compactness comes from the earlier
    original support laws, not a measure representation. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentCoefficientNorms CurrentSpaces CurrentEvaluation
  CurrentContraction CurrentCompactExtensionUP CurrentCompactExtensionSealed
  CurrentCompactSmoothValue SmoothCurrentFormProduct CurrentTestFormProduct
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionTopology
  SmoothTestSpaces SmoothDualRestriction ContinuousRealDual ContinuousRealDualTranspose.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CompactContraction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E:=(fun j=>@current_smooth_space R h2 n U hU j).
Local Notation ev:=(fun j=>@current_smooth_value R h2 n U hU j).
Local Notation hE:=(fun j=>@current_smooth_space_laws R h2 n U hU j).
Local Notation D:=(fun j=>@current_smooth_derivatives R h2 n U hU j).
Local Notation hD:=(fun j=>@current_smooth_derivative_laws R h2 n U hU j).
Local Notation O:=(fun j=>smooth_function_opens (hD j)).
Local Notation hO:=(fun j=>(smooth_function_topology_laws (hD j)).1).
Variable gamma:E k.
Variable T:@current_space R h2 n U hU (k+p).
Hypothesis hCompact:@compact (real_norm_metric_space hNX)
  (@current_support R h2 n U hU (k+p) T).
Local Notation S:=(@current_contraction R h2 n k p U hU gamma T).
Hypothesis hContractCompact:@compact (real_norm_metric_space hNX)
  (@current_support R h2 n U hU p S).
Local Notation P:=(@smooth_current_form_product R h2 n k p U hU gamma).
Local Notation Pt:=(@current_test_form_product R h2 n k p U hU gamma).
Local Notation hP:=(@smooth_current_form_product_continuous R h2 n k p U hU gamma).
Local Notation LT:=(@CompactCurrentExtension.value R h2 n (k+p) U hU T hCompact).
Local Notation LS:=(@CompactCurrentExtension.value R h2 n p U hU S hContractCompact).
Local Notation eE:=(@continuous_real_dual_evaluation R (E p) (O p) (hO p)).
Local Notation eF:=(@continuous_real_dual_evaluation R (E (k+p)) (O (k+p)) (hO (k+p))).

(** Source for [current_compact_contraction_smooth_value]: the
    original contraction identity also holds on smooth forms
    through the unique compact-current extension. This is the
    scalar-contraction evaluation used in Federer 4.1.20, p. 378,
    from 4.1.7, pp. 355–356. Each compactness proof indexes that
    same earlier extension; no density or finite mass is assumed. *)
Theorem current_compact_contraction_smooth_value (phi:E p):
  @current_compact_smooth_value R h2 n p U hU S hContractCompact phi=
  @current_compact_smooth_value R h2 n (k+p) U hU T hCompact (P phi).
Proof.
pose Q:=@continuous_real_dual_transpose R (E p) (E (k+p))
  (O p) (O (k+p)) (hO p) (hO (k+p)) P hP.
have hRestriction:@current_smooth_dual_restriction R h2 n U hU p (Q LT)=S.
  apply:(@current_values_extensional R h2 n p U hU)=>psi.
  have hValue:=@smooth_dual_test_restriction_evaluation R X (A_m X R^o p)
    NX (@current_form_comass R h2 n p) hNX (@current_form_comass_real_norm R h2 n p)
    U (E p) (ev p) (hE p) (D p) (hD p) (Q LT) psi.
  have hTranspose:=@continuous_real_dual_transpose_evaluation R (E p) (E (k+p))
    (O p) (O (k+p)) (hO p) (hO (k+p)) P hP LT (smooth_test_inclusion (hE p) psi).
  have hProduct:P (smooth_test_inclusion (hE p) psi)=
      smooth_test_inclusion (hE (k+p)) (Pt psi).
    exact:esym (@current_test_form_product_inclusion R h2 n k p U hU gamma psi).
  rewrite hProduct in hTranspose.
  have hTest:=@current_compact_smooth_test_value R h2 n (k+p) U hU
    T hCompact (Pt psi).
  have hContract:=@current_contraction_evaluation R h2 n k p U hU gamma T psi.
  exact:(eq_trans hValue (eq_trans hTranspose (eq_trans hTest (esym hContract)))).
have hEqual:LS=(Q LT:@current_smooth_dual_space R h2 n U hU p).
  apply:(@current_compact_extension_unique R h2 n p U hU S).
  - exact:(@CompactCurrentExtension.laws R h2 n p U hU S hContractCompact).
  - exact:hRestriction.
change (eE LS phi=eF LT (P phi));rewrite hEqual.
exact:(@continuous_real_dual_transpose_evaluation R (E p) (E (k+p))
  (O p) (O (k+p)) (hO p) (hO (k+p)) P hP LT phi).
Qed.
End CompactContraction.
