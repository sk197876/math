(** Federer (1969), 4.1.18, pp. 374–375:
    use the already opaque compact form average
    with the original reflected smoothing kernel.
    Its scalar-action law and exterior commutation
    retain the original source and all form degrees. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap CurrentSpaces CurrentCartesianDomain SmoothCompactSet
  CurrentKernelAverageUP CurrentKernelAverageSealed CurrentKernelAverageBounds
  CurrentCompactKernelFormAverageUP CurrentCompactKernelFormAverageSealed
  CurrentCompactKernelFormAverageExterior SmoothCurrentExteriorDerivative
  SmoothingKernelUP SmoothingDilationUP SmoothingReflectedWeight.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentCompactSmoothingFormAverage.
Variable R:realType.
Hypothesis h2:(1+1:R)!= 0.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation AB:=(@euclidean_cartesian_set R n n Full Full).
Local Notation hAB:=(@current_cartesian_domain_open R n n Full Full hFull hFull).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation w:=(fun z:X=>family epsilon (-z)).
Local Notation S:=(@CurrentKernelAverage.value R h2 n phi family hPhi hFamily epsilon hEpsilon).
Local Notation hS:=(@CurrentKernelAverage.laws R h2 n phi family hPhi hFamily epsilon hEpsilon).
Local Notation K:=(@current_kernel_average_index R n epsilon).

(** Source for [current_compact_smoothing_form_average_off]:
    the original reflected kernel vanishes off its
    actual compact ball, supporting the smoothing
    form integral in 4.1.18, pp. 374–375. *)
Lemma current_compact_smoothing_form_average_off z:
  ~smooth_compact_carrier K z->w z= 0.
Proof.
move=>hz;have hFar:epsilon<NX z.
  rewrite ltNge;apply/negP=>hRadius;apply:hz.
  by rewrite current_kernel_average_index_carrier.
exact:(@smoothing_reflected_weight_off R n phi family hPhi hFamily epsilon hEpsilon z hFar).
Qed.

(** Source for [current_compact_smoothing_form_average]: the
    original compact reflected-kernel average, using
    only the preceding opaque form integral,
    supporting 4.1.18, p. 375. *)
Definition current_compact_smoothing_form_average j:
    Hom (@current_smooth_space R h2 (n+n)%N AB hAB j)
      (@current_smooth_space R h2 n Full hFull j):=
  @CurrentCompactKernelFormAverage.value R h2 n n j Full hFull w S hS K
    current_compact_smoothing_form_average_off.

(** Source for [current_compact_smoothing_form_average_laws]:
    its independent literal coefficient-integral law,
    supporting 4.1.18, pp. 374–375. *)
Theorem current_compact_smoothing_form_average_laws j:
  @is_current_compact_kernel_form_average R h2 n n j Full hFull w
    (current_compact_smoothing_form_average j).
Proof.
exact:(@CurrentCompactKernelFormAverage.laws R h2 n n j Full hFull w S hS K
  current_compact_smoothing_form_average_off).
Qed.

(** Source for [current_compact_smoothing_form_average_exterior]:
    the actual average commutes with the original
    spatial exterior differential, supporting
    the form homotopy of 4.1.18, p. 375. *)
Theorem current_compact_smoothing_form_average_exterior j
    (omega:@current_smooth_space R h2 (n+n)%N AB hAB j):
  @smooth_current_exterior_derivative R h2 n j Full hFull
    (current_compact_smoothing_form_average j omega)=
  current_compact_smoothing_form_average j.+1
    (@smooth_current_exterior_derivative R h2 (n+n)%N j AB hAB omega).
Proof.
exact (@current_compact_kernel_form_average_exterior R h2 n n j Full hFull
  w S hS K current_compact_smoothing_form_average_off
  (current_compact_smoothing_form_average j) (current_compact_smoothing_form_average j.+1)
  (@current_compact_smoothing_form_average_laws j)
  (@current_compact_smoothing_form_average_laws j.+1) omega).
Qed.
End CurrentCompactSmoothingFormAverage.
