(** Federer (1969), 4.1.7, pp. 358–359:
    a scalar cutoff equal to one on
    a test support leaves that test unchanged.
    Use the actual pointwise exterior product. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero AlternatingProduct ScalarCoefficients
  ZeroFormScalarProduct CurrentCoefficientNorms CurrentSpaces CurrentTestFormProduct CurrentSupportGeometry
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentScalarPlateau.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation E0 := (@current_smooth_space R h2 n U hU 0%N).
Local Notation DT := (@current_test_space R h2 n U hU m).

(** Source for [current_scalar_test_plateau]: multiplication
    by a smooth scalar equal to one on
    K fixes every original test supported in
    K, supporting Federer 4.1.7, pp. 358–359. *)
Theorem current_scalar_test_plateau (K:smooth_compact_set hNX U) (gamma:E0):
  (forall x,smooth_compact_carrier K x->
    @current_smooth_value R h2 n U hU 0%N gamma x=@zero_form R X R^o 1) ->
  forall psi:DT,@current_test_support R h2 n m U hU psi `<=` smooth_compact_carrier K ->
    @current_test_form_product R h2 n 0 m U hU gamma psi=psi.
Proof.
move=>hGamma psi hPsi.
have hZero:=(@smooth_function_compact_support_iff R X (A_m X R^o m) NX
  (@current_form_comass R h2 n m) hNX (@current_form_comass_real_norm R h2 n m)
  U (@current_smooth_space R h2 n U hU m) (@current_smooth_value R h2 n U hU m)
  hE K (smooth_test_inclusion hE psi)).1 hPsi.
apply:(smooth_test_values_extensional hE)=>x hx.
change (@current_test_value R h2 n U hU m
  (@current_test_form_product R h2 n 0 m U hU gamma psi) x=
    @current_test_value R h2 n U hU m psi x).
rewrite (@current_test_form_product_values R h2 n 0 m U hU gamma psi x hx).
case:(pselect (smooth_compact_carrier K x))=>hKx.
- by rewrite (hGamma x hKx) original_zero_form_wedge_scalar scale1r.
- have hOff:@current_test_value R h2 n U hU m psi x=0:=@hZero x hKx.
  rewrite hOff.
  exact:(bil0r (@form_wedge_bilinear R h2 X R^o _ (scalar_bilinear R) 0 m)).
Qed.

(** Source for [current_scalar_test_local_plateau]:
    a scalar equal to one on W
    fixes every original test supported in
    W, supporting the near-point normality
    criterion in Federer 4.1.7, p. 358. *)
Theorem current_scalar_test_local_plateau (W:set X) (gamma:E0):
  (forall x,W x->@current_smooth_value R h2 n U hU 0%N gamma x=@zero_form R X R^o 1) ->
  forall psi:DT,@current_test_support R h2 n m U hU psi `<=` W ->
    @current_test_form_product R h2 n 0 m U hU gamma psi=psi.
Proof.
move=>hGamma psi hPsi.
pose K:=@Build_smooth_compact_set R X NX hNX U
  (@current_test_support R h2 n m U hU psi) (fun x hx=>hx.1)
  (@smooth_test_support_compact R X (A_m X R^o m) NX (@current_form_comass R h2 n m)
    hNX (@current_form_comass_real_norm R h2 n m) U
    (@current_smooth_space R h2 n U hU m) (@current_smooth_value R h2 n U hU m) hE psi).
apply:(@current_scalar_test_plateau K gamma _ psi (fun x hx=>hx))=>x hx.
exact:hGamma x (hPsi x hx).
Qed.
End CurrentScalarPlateau.
