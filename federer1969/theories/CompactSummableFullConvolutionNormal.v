(** Federer (1969), 4.1.18, p. 375: ordinary
    smooth field convolutions give original normal
    density currents with support in the exact
    epsilon tube. The old normality criterion and
    the proved arbitrary-current smoothing laws suffice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentSpaces CurrentDomain CurrentCoefficientNorms CurrentSupportGeometry SmoothCompactSet
  NormalCurrentsUP CurrentSmoothingOperators CurrentSmoothingNormality CurrentSmoothingSupportTube
  CurrentOpenRestriction CurrentOpenRestrictionNormal CurrentOpenRestrictionSupport
  CompactSummableMultivectors CompactSummableMultivectorAmbient CompactSummableMultivectorSupport
  CompactSummableMultivectorDensity CompactSummableFullConvolutionMass
  SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP SmoothingKernelReflection
  EuclideanClosedSupportTube.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FullConvolutionNormal.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation FT:=(current_domain R n Full).
Local Notation W:=(@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation value:=(@compact_summable_multivector_value R h2 n m Full hFull).
Local Notation raw:=(@compact_summable_multivector_ambient_value R h2 n m Full hFull).
Local Notation fieldSupport:=(@compact_summable_multivector_ambient_support R h2 n m Full hFull).
Local Notation A:=(@compact_summable_multivector_current R h2 n m Full hFull).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).

(** Source for [compact_summable_full_current_support]:
    the literal coefficient support bounds the actual
    density-current support, supporting the normal
    approximation in 4.1.18, p. 375. *)
Theorem compact_summable_full_current_support (xi:W):
  @current_support R h2 n Full hFull m (A xi) `<=` fieldSupport xi.
Proof.
pose K:=@Build_smooth_compact_set R X NX hNX Full (fieldSupport xi)
  (fun _ _=>Logic.I)
  (@compact_summable_multivector_ambient_support_laws R h2 n m Full hFull xi).1.
apply:(@compact_summable_multivector_current_support R h2 n m Full hFull xi K)=>x hx.
rewrite -(compact_summable_multivector_ambient_inside xi x).
exact:((@compact_summable_multivector_ambient_support_laws R h2 n m Full hFull xi).2.2
  (set_val x) hx).
Qed.

(** Source for [compact_summable_full_current_compact]:
    an original Omega field has compact actual
    current support, supporting 4.1.18, p. 375. *)
Theorem compact_summable_full_current_compact (xi:W):
  @compact XT (@current_support R h2 n Full hFull m (A xi)).
Proof.
pose K:=@Build_smooth_compact_set R X NX hNX Full (fieldSupport xi)
  (fun _ _=>Logic.I)
  (@compact_summable_multivector_ambient_support_laws R h2 n m Full hFull xi).1.
apply:(@current_support_compact_bound R h2 n m Full hFull K (A xi)).
exact:(@compact_summable_full_current_support xi).
Qed.

Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.

(** Source for [compact_summable_full_convolution_normal]:
    the actual density of ordinary Phi_epsilon*xi
    is a normal current supported in the literal
    epsilon tube, supporting the first proposition
    of Federer 4.1.18, p. 375. *)
Theorem compact_summable_full_convolution_normal (xi zeta:W):
  is_smoothing_convolution hVN (family epsilon) (raw xi) (raw zeta) ->
  @is_normal_current R h2 n Full hFull m (A zeta) /\
  (@current_support R h2 n Full hFull m (A zeta) `<=`
    @euclidean_closed_support_tube R n (fieldSupport xi) epsilon).
Proof.
move=>hConv.
have hImage:=@compact_summable_full_convolution_current R h2 n m
  phi family hPhi hFamily epsilon hEpsilon xi zeta hConv.
rewrite hImage;split.
- apply:(@current_smoothing_normal R h2 n
    (fun x:X=>phi (-x)) (fun e x=>family e (-x))
    (@smoothing_reflected_kernel_laws R n phi hPhi)
    (@smoothing_reflected_dilation_laws R n phi family hFamily)
    epsilon hEpsilon m (A xi)).
  exact:(@compact_summable_full_current_compact xi).
- move=>x hx.
  have hTube:=@current_smoothing_support_tube R h2 n m
    (fun x:X=>phi (-x)) (fun e x=>family e (-x))
    (@smoothing_reflected_kernel_laws R n phi hPhi)
    (@smoothing_reflected_dilation_laws R n phi family hFamily)
    epsilon hEpsilon (A xi) x hx.
  exact:(@euclidean_closed_support_tube_mono R n _ _ epsilon epsilon
    (@compact_summable_full_current_support xi) (lexx epsilon) x hTube).
Qed.

(** Source for [compact_summable_open_convolution_normal]:
    restricting an ordinary smoothing to its original
    U preserves normality whenever its literal support
    tube lies in U, Federer 4.1.18, p. 375. *)
Theorem compact_summable_open_convolution_normal
    (U:set X) (hU:forall x,U x->norm_domain_interior NX U x) (xi zeta:W):
  is_smoothing_convolution hVN (family epsilon) (raw xi) (raw zeta) ->
  (@euclidean_closed_support_tube R n (fieldSupport xi) epsilon `<=` U)->
  @is_normal_current R h2 n U hU m
    (@current_open_restriction R h2 n m U Full hU hFull
      (fun _ _=>Logic.I) (A zeta)).
Proof.
move=>hConv hTube.
have[hNormal hSupport]:=compact_summable_full_convolution_normal hConv.
apply:(@current_normal_neighbourhood_restriction R h2 n U Full hU hFull
  (fun _ _=>Logic.I) m (A zeta) hNormal).
exact:subset_trans hSupport hTube.
Qed.
End FullConvolutionNormal.
