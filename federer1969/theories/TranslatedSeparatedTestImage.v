(** Federer (1969), 4.1.3, p. 348: every translated
    dilated separated-kernel test is a pure tensor image.
    The exact epsilon power is absorbed in its vector factor;
    each scalar affine factor is an actual one-variable test. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation SmoothingDilationUP TranslatedKernelTestUP
  TestTensorMapUP TestLineAffinePrecomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section TranslatedSeparatedTestImage.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hR := (@scalar_absolute_value_norm R).
Variable A:lmodType R.
Variable av:A->R^o->R^o.
Hypothesis hA:is_smooth_function_space hR hR (fun _=>True) av.
Local Notation D1 := (smooth_test_space hA).
Variable gamma:D1.
Local Notation phi := (fun x:X=>\prod_i smooth_test_value hA gamma (x i)).
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation Dn := (smooth_test_space hE).
Variable T W:lmodType R.
Variable mu:{dffun forall i:'I_n,D1}->T.
Variable nu:T->Y->W.
Variable F:Hom W Dn.
Hypothesis hF:is_test_tensor_map hA hE mu nu F.

(** Source for [translated_separated_test_in_tensor_image]:
    the original kernel summands belong to the canonical tensor
    image, Federer 4.1.3, p. 348. *)
Theorem translated_separated_test_in_tensor_image
    e (he:0<e) (B:X->Hom Y Dn):
  @is_translated_kernel_tests R X Y _ NY hN hNY E ev hE (family e) B ->
  forall z y,exists w:W,F w=B z y.
Proof.
move=>hB z y.
have hInv:e^-1!=0 by rewrite invr_eq0 (gt_eqF he).
have hEach i:=@test_line_affine_precomposition_exists R A av hA gamma e^-1 (z i) hInv.
have[g hg]:=choice hEach.
pose f:{dffun forall i:'I_n,D1}:=[ffun i=>g i].
exists (nu (mu f) ((e^+n)^-1*:y)).
apply:(smooth_test_values_extensional hE)=>x _.
rewrite hF hB (@hFamily e he (x-z)).
have hProduct:(\prod_i smooth_test_value hA (f i) (x i))=
    \prod_i smooth_test_value hA gamma ((e^-1*:(x-z)) i).
  apply:eq_bigr=>i _.
  by rewrite /f ffunE (hg i) !ffunE.
rewrite hProduct; by rewrite scalerA mulrC.
Qed.
End TranslatedSeparatedTestImage.
