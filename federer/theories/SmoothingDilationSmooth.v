(** Federer (1969), 4.1.2, pp. 346–347:
    every positive-scale kernel dilation is nonnegative
    and smooth. The earlier affine-dilation calculus
    supplies every order of smoothness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ContinuousMultilinearSealed NormClassHigherUP NormRegularity NormRegularityOperations
  NormAffineDilationDifferentials SmoothingKernelUP SmoothingDilationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothingDilationSmooth.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hR := (@scalar_absolute_value_norm R).
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.

(** Source for [smoothing_dilation_nonnegative]: the
    rescaled nonnegative kernel remains nonnegative,
    Federer 4.1.2, p. 346. *)
Theorem smoothing_dilation_nonnegative e:0<e ->forall x,0<=family e x.
Proof.
move=>he x; rewrite (@hFamily e he x).
have hCoeff:0<(e^+n)^-1 by rewrite invr_gt0; exact:exprn_gt0.
exact:mulr_ge0 (ltW hCoeff) (@smoothing_kernel_nonnegative R n phi hPhi (e^-1*:x)).
Qed.

(** Source for [smoothing_dilation_smooth]: each rescaled
    kernel has every original differentiability class,
    Federer 4.1.2, pp. 346–347. *)
Theorem smoothing_dilation_smooth e:0<e ->norm_class_all_orders hN hR (fun _=>True) (family e).
Proof.
move=>he.
pose Z:=fun j=>@ContinuousMultilinear.space R j X R^o N (fun t:R^o=>`|t|) hN hR.
pose ev:=fun j=>@ContinuousMultilinear.evaluation R j X R^o N (fun t:R^o=>`|t|) hN hR.
pose ZN:=fun j=>@ContinuousMultilinear.norm R j X R^o N (fun t:R^o=>`|t|) hN hR.
pose hZ:=fun j=>@ContinuousMultilinear.laws R j X R^o N (fun t:R^o=>`|t|) hN hR.
have hCompose:=@norm_class_infinity_affine_dilation R X R^o N (fun t:R^o=>`|t|) hN hR
  Z ev ZN hZ phi e^-1 0 (smoothing_kernel_smooth hPhi).
move=>k.
have hScaled:norm_class hN hR (fun _=>True)
    (fun x=>(e^+n)^-1*phi (e^-1*:x+0)) k.
  exact:(norm_class_scale (e^+n)^-1 (hCompose k)).
have hEq:(fun x:X=>(e^+n)^-1*phi (e^-1*:x+0))=family e.
  apply:funext=>x; rewrite addr0 (@hFamily e he x); reflexivity.
by rewrite hEq in hScaled.
Qed.
End SmoothingDilationSmooth.
