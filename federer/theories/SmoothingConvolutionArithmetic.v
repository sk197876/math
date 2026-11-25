(** Federer (1969), 4.1.18, p. 375: ordinary
    convolution is linear on the original summable
    field inputs. This is the actual vector integral
    subtraction law of 2.4.12, pp. 87–88. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations
  EuclideanLebesgueDimensions SmoothingConvolutionUP
  TotalVectorIntegralArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [smoothing_convolution_subtract]: subtraction
    of the literal ordinary field convolutions in
    Federer 4.1.18, p. 375. No symmetry of
    the convolution kernel is used. *)
Theorem smoothing_convolution_subtract (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (kernel:R_n R n->R) (f g a b:R_n R n->Y):
  is_smoothing_convolution hNY kernel f a ->
  is_smoothing_convolution hNY kernel g b ->
  is_smoothing_convolution hNY kernel (fun x=>f x-g x)
    (fun x=>a x-b x).
Proof.
move=>hA hB x.
have h:=@total_vector_integral_subtract R (R_n R n) Y NY hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (fun z=>kernel (x-z)*:f z) (fun z=>kernel (x-z)*:g z)
  (a x) (b x) (hA x) (hB x).
have hFunction:(fun z=>kernel (x-z)*:f z-kernel (x-z)*:g z)=
    (fun z=>kernel (x-z)*:(f z-g z)).
  apply:funext=>z;by rewrite scalerBr.
by rewrite hFunction in h.
Qed.
