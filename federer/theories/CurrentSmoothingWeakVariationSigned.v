(** Federer (1969), 4.1.18, p. 375: the
    original variation weak limit holds on every
    signed compact continuous test, by the old
    positive/negative decomposition. No global finite
    variation is required.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentIntegrationCriterion CurrentAmbientVariation
  CurrentSmoothingOperators CurrentSmoothingRepresentable CurrentSmoothingWeakVariation
  SmoothingKernelUP SmoothingDilationUP CompactSupportFunctionUP
  RadonCompactScalarIntegral RadonCompactIntegralPositiveParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentSmoothingWeakVariationSigned.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable T:@current_space R h2 n Full hFull m.
Hypothesis hT:@is_integration_representable_current R h2 n m Full hFull T.
Local Notation Smooth:=(@current_smoothing R h2 n m phi family hPhi hFamily T).
Local Notation hSmooth:=(@current_smoothing_representable R h2 n m phi family hPhi hFamily T).
Local Notation PositiveIntegral:=(@current_smoothing_ambient_variation_integral R h2 n m
  phi family hPhi hFamily T).
Local Notation mu:=(@current_ambient_variation R h2 n m T hT).
Local Notation hm:=(@current_ambient_variation_laws R h2 n m T hT).1.
Local Notation hr:=(@current_ambient_variation_laws R h2 n m T hT).2.
Local Notation D:=(@radon_compact_integral R XT mu hm hr).

(** Source for [current_smoothing_weak_variation_signed]:
    ||T_epsilon||(f) tends to ||T||(f) for every
    signed original f in K(R^n), the full Daniell
    weak convergence in Federer 4.1.18, p. 375. *)
Theorem current_smoothing_weak_variation_signed (f:XT->R):
  compactly_supported_continuous_functions f ->
  forall eta:R,0<eta ->exists r:R,0<r /\
    forall epsilon:R,forall he:0<epsilon,epsilon<r ->
    `|@radon_compact_integral R XT
      (@current_ambient_variation R h2 n m (Smooth epsilon) (hSmooth epsilon he))
      (@current_ambient_variation_laws R h2 n m (Smooth epsilon) (hSmooth epsilon he)).1
      (@current_ambient_variation_laws R h2 n m (Smooth epsilon) (hSmooth epsilon he)).2 f-
      D f|<eta.
Proof.
move=>hF eta hEta.
have [hPlus [hMinus _]]:=compact_function_positive_parts hF.
have hHalf:0<eta/2 by rewrite divr_gt0 // ltr0n.
have [rP [hrP hP]]:=@current_smoothing_weak_variation R h2 n m phi family hPhi hFamily
  T hT (fun x=>Order.max (f x) 0) hPlus (eta/2) hHalf.
have [rM [hrM hM]]:=@current_smoothing_weak_variation R h2 n m phi family hPhi hFamily
  T hT (fun x=>Order.max (-f x) 0) hMinus (eta/2) hHalf.
exists (Order.min rP rM);split;first by rewrite lt_min hrP hrM.
move=>epsilon he heSmall.
have hRP:Order.min rP rM<=rP by rewrite ge_min lexx.
have hRM:Order.min rP rM<=rM by rewrite ge_min lexx orbT.
have hPos:=hP epsilon he (lt_le_trans heSmall hRP).
have hNeg:=hM epsilon he (lt_le_trans heSmall hRM).
rewrite (radon_compact_integral_positive_parts
  (@current_ambient_variation_laws R h2 n m (Smooth epsilon) (hSmooth epsilon he)).1
  (@current_ambient_variation_laws R h2 n m (Smooth epsilon) (hSmooth epsilon he)).2 hF)
  (radon_compact_integral_positive_parts hm hr hF).
pose a:=@current_smoothing_ambient_variation_integral R h2 n m phi family hPhi hFamily T
  epsilon he (fun x=>Order.max (f x) 0).
pose b:=@current_smoothing_ambient_variation_integral R h2 n m phi family hPhi hFamily T
  epsilon he (fun x=>Order.max (-f x) 0).
pose c:=@radon_positive_compact_integral R XT mu hm hr (fun x=>Order.max (f x) 0).
pose d:=@radon_positive_compact_integral R XT mu hm hr (fun x=>Order.max (-f x) 0).
change (is_true (`|(a-b)-(c-d)|<eta)).
have hDecompose:(a-b)-(c-d)=(a-c)-(b-d) by ring.
rewrite hDecompose.
have hTriangle:=ler_normD (a-c) (-(b-d)).
rewrite normrN in hTriangle.
have hSum:=ltrD hPos hNeg.
rewrite -splitr in hSum.
exact:(le_lt_trans hTriangle hSum).
Qed.
End CurrentSmoothingWeakVariationSigned.
