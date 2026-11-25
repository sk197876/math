(** Federer (1969), 4.1.15, p. 372: the two smoothed
    maps agree where the original inputs agree throughout the
    smoothing ball. This is a direct consequence of the actual
    vector integral in 4.1.2, p. 347. No extension of an input
    outside its original domain is assumed by the local law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness
  PartialFunctionBasic MeasureVectorIntegralUP SmoothingConvolutionUP
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationNonzeroRadius.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [smoothing_convolution_agree_at]: equal inputs at
    every point contributing to the convolution give the same
    smoothed value, as used for the displayed agreement set in
    Federer 4.1.15, p. 372. Existence of either integral is not
    postulated: both are the given original convolution laws. *)
Theorem smoothing_convolution_agree_at (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (phi:R_n R n->R) (F G a b:R_n R n->Y):
  is_smoothing_convolution hNY phi F a ->
  is_smoothing_convolution hNY phi G b ->
  forall x,(forall z,phi (x-z)!=0->F z=G z)->a x=b x.
Proof.
move=>hF hG x hAgreement.
have hIntegrands:
    (fun z:R_n R n=>(phi (x-z)*:F z:real_norm_metric_space hNY))=
    (fun z:R_n R n=>(phi (x-z)*:G z:real_norm_metric_space hNY)).
  apply:funext=>z.
  case:(pselect (phi (x-z)=0))=>[hZero|hNonzero].
  - by rewrite hZero !scale0r.
  - have hNZ:phi (x-z)!=0 by apply/eqP;exact:hNonzero.
    by rewrite (@hAgreement z hNZ).
have hIntegral:=hF x.
rewrite hIntegrands in hIntegral.
exact:(measure_vector_integral_unique hIntegral (hG x)).
Qed.

(** Source for [smoothing_convolution_closed_ball_agreement]: the
    literal closed-ball condition in the agreement locus of
    Federer 4.1.15, p. 372, implies equality of the two
    smoothed values. The proved support of Phi_epsilon lies
    inside that ball, by 4.1.2, pp. 346–347. *)
Theorem smoothing_convolution_closed_ball_agreement (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (phi:R_n R n->R) (family:R->R_n R n->R)
    (F G a b:R_n R n->Y) (epsilon:R):
  is_smoothing_kernel phi ->is_smoothing_dilation phi family ->
  0<epsilon ->
  is_smoothing_convolution hNY (family epsilon) F a ->
  is_smoothing_convolution hNY (family epsilon) G b ->
  forall x,(forall z,
    inner_norm (@euclidean_inner_productP R n) (x-z)<=epsilon->F z=G z)->
  a x=b x.
Proof.
move=>hPhi hFamily hEpsilon hF hG x hAgreement.
apply:(@smoothing_convolution_agree_at R n Y NY hNY
  (family epsilon) F G a b hF hG x)=>z hz.
apply:(@hAgreement z).
exact:(ltW (@smoothing_dilation_nonzero_radius R n phi family
  hPhi hFamily epsilon hEpsilon (x-z) hz)).
Qed.
