(** Federer (1969), 4.1.15, p. 372: Phi_epsilon*f
    and Phi_epsilon*G_r agree on the displayed closed-ball
    locus. The actual convolution integrals and the original
    radial value law suffice. G_r takes values in ambient
    Euclidean space; no target-image assertion is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct SmoothingKernelUP
  SmoothingDilationUP SmoothingConvolutionUP SmoothingConvolutionLocalAgreement
  RadialAgreementMapUP RadialAgreementMapBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radial_smoothing_agreement_locus]: the
    original Z_(r,epsilon) in Federer 4.1.15, p. 372.
    The ball is closed, so its boundary is retained. *)
Definition radial_smoothing_agreement_locus (R:realType) n nu
    (U:set (R_n R n)) (f g:R_n R n->R_n R nu) (r epsilon:R):set (R_n R n):=
  [set x|U x /\ forall z,
    inner_norm (@euclidean_inner_productP R n) (x-z)<=epsilon->
    inner_norm (@euclidean_inner_productP R nu) (g z-f z)<r].

(** Source for [radial_smoothing_agreement]: the two
    actual smoothings agree on Z_(r,epsilon), Federer
    4.1.15, p. 372. Both original convolution laws
    remain explicit, so no undefined smoothing value is
    introduced at a source-domain boundary. *)
Theorem radial_smoothing_agreement (R:realType) n nu
    (U:set (R_n R n)) (f g G:R_n R n->R_n R nu)
    (r:R) (hr:0<r) (hG:@is_radial_agreement_map R n nu r hr f g G)
    (phi:R_n R n->R) (family:R->R_n R n->R)
    (epsilon:R) (a b:R_n R n->R_n R nu):
  is_smoothing_kernel phi ->is_smoothing_dilation phi family ->
  0<epsilon ->
  is_smoothing_convolution (inner_norm_real_norm (@euclidean_inner_productP R nu))
    (family epsilon) f a ->
  is_smoothing_convolution (inner_norm_real_norm (@euclidean_inner_productP R nu))
    (family epsilon) G b ->
  forall x,radial_smoothing_agreement_locus U f g r epsilon x->a x=b x.
Proof.
move=>hPhi hFamily hEpsilon hA hB x [_ hLocus].
apply:(@smoothing_convolution_closed_ball_agreement R n (R_n R nu)
  (inner_norm (@euclidean_inner_productP R nu))
  (inner_norm_real_norm (@euclidean_inner_productP R nu))
  phi family f G a b epsilon hPhi hFamily hEpsilon hA hB x)=>z hz.
exact:(esym (@radial_agreement_closed_locus R n nu r hr f g G hG z
  (ltW (@hLocus z hz)))).
Qed.
