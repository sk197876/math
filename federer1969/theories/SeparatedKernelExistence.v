(** Federer (1969), 4.1.3, p. 348: an actual normalized
    smoothing kernel can be chosen as the coordinate product of
    one scalar test. Use the sealed one-dimensional kernel of
    4.1.2 at radius 1/(n+1), then the original finite-product
    Fubini theorem. The construction proves existence only. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import RealNormUP GrassmannAbbreviations SmoothFunctionSpaceUP
  SmoothTestSpaces SmoothTestEvaluation SmoothingKernelUP SmoothingKernelSealed
  SmoothingDilationUP SmoothingDilationSealed ScalarLineSmoothingTest SeparatedSmoothingKernel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [separated_kernel_exists]: the common test gamma
    in the displayed formula of Federer 4.1.3, p. 348, can
    satisfy every kernel requirement of 4.1.2, p. 346. *)
Theorem separated_kernel_exists (R:realType) n (A:lmodType R)
    (av:A->R^o->R^o)
    (hA:is_smooth_function_space (@scalar_absolute_value_norm R)
      (@scalar_absolute_value_norm R) (fun _=>True) av):
  exists gamma:smooth_test_space hA,
    is_smoothing_kernel (fun x:R_n R n=>\prod_i smooth_test_value hA gamma (x i)).
Proof.
pose phi:=@SmoothingKernel.value R 1.
have hPhi:=@SmoothingKernel.laws R 1.
pose family:=@SmoothingDilation.value R 1 phi.
have hFamily:=@SmoothingDilation.laws R 1 phi.
pose r:=((n.+1)%:R:R)^-1.
have hDen:0<((n.+1)%:R:R) by rewrite ltr0n.
have hr:0<r by rewrite /r invr_gt0.
have hSmall:(n%:R:R)*r<1.
  by rewrite /r ltr_pdivrMr // mul1r ltr_nat.
have[gamma [_ [hNonnegative [hSupport hIntegral]]]]:=
  @scalar_line_smoothing_test_exists R A av hA phi hPhi family hFamily r hr.
exists gamma.
exact:(@separated_smoothing_kernel_laws R n A av hA gamma r
  hSmall hNonnegative hSupport hIntegral).
Qed.
