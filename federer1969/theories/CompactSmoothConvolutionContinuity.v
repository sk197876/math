(** Federer (1969), 4.1.2, p. 347: convolution
    by a smooth compact scalar kernel is continuous.
    The compact-uniform continuity of the kernel and
    local norm integrability supply the original estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormClassOneUP NormRegularity
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness FiniteNormEquivalence
  SmoothCompactSet CompactNearbyUniformContinuity MeasureUP EuclideanLebesgueDimensions
  LocallyIntegrableVectorFieldUP SmoothingConvolutionUP CompactKernelSourceBall WeightedVectorIntegralError.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_smooth_convolution_continuous]: class
    zero of the original convolution in Federer 4.1.2,
    p. 347. Only one local compact
    norm integral is used at each centre. *)
Theorem compact_smooth_convolution_continuous (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (f g:R_n R n->Y) (psi:R_n R n->R) r:
  @is_locally_integrable_vector_field R (R_n R n) Y
    (inner_norm (@euclidean_inner_productP R n)) NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY
    (@euclidean_lebesgue_measure R n) f ->
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@scalar_absolute_value_norm R) (fun _=>True) psi ->
  (forall z,r<inner_norm (@euclidean_inner_productP R n) z ->psi z=0) ->
  is_smoothing_convolution hNY psi f g ->
  norm_class_zero (inner_norm (@euclidean_inner_productP R n)) NY (fun _=>True) g.
Proof.
move=>hField hPsi hOff hConvolution a _.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
split; first exact:norm_full_domain_interior.
move=>e he.
pose K:=@Build_smooth_compact_set R X N hN (fun _=>True)
  [set z|N (z-a)<=r+1] (fun _ _=>Logic.I)
  (@finite_norm_closed_ball_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN a (r+1)).
have [b hLocal]:=@locally_integrable_vector_compact_norm R X Y N NY hN hNY
  (@euclidean_lebesgue_measure R n) f hField K.
pose c:=e/(`|b|+1).
have hDen:0<`|b|+1 by have:=normr_ge0 b; lra.
have hc:0<c by rewrite /c divr_gt0.
have hcValue:c*(`|b|+1)=e by rewrite /c divfK // gt_eqF.
pose L:=[set w:X|N (w-0)<=r+1].
have hL:@compact (real_norm_metric_space hN) L.
  exact:(@finite_norm_closed_ball_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN 0 (r+1)).
have [d [hd hUniform]]:=@norm_class_zero_compact_uniform_nearby R X R^o N (fun t:R^o=>`|t|)
  hN (@scalar_absolute_value_norm R) (fun _=>True) L psi hL (fun _ _=>Logic.I)
  (norm_class_continuous (hPsi 0%N)) c hc.
exists (Num.min d 1); split; first by rewrite lt_min hd ltr01.
move=>h _ hh.
have hSmall:N h<1.
  apply:(lt_le_trans hh).
  by rewrite ge_min lexx orbT.
have hD:N h<d.
  apply:(lt_le_trans hh).
  by rewrite ge_min lexx.
have hError:=@weighted_vector_integral_difference_bound R X Y NY hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (smooth_compact_carrier K) f (fun z=>psi (a+h-z)) (fun z=>psi (a-z))
  (g (a+h)) (g a) b c hLocal (hConvolution (a+h)) (hConvolution a).
have hBound z:smooth_compact_carrier K z ->`|psi (a+h-z)-psi (a-z)|<=c.
  move=>hz.
  have hBase:L (a-z).
    change (is_true (N (a-z-0)<=r+1)).
    have hSym:N (a-z)=N (z-a):=real_seminorm_subtract hN.1 a z.
    rewrite subr0 hSym; exact hz.
  have hStep:N ((a+h-z)-(a-z))<d.
    have hShift:a+h-z=(a-z)+h by rewrite addrAC.
    have hEq:(a+h-z)-(a-z)=h by rewrite hShift addrAC subrr add0r.
    by rewrite hEq.
  exact:ltW (hUniform (a-z) (a+h-z) hBase Logic.I hStep).
have hZero z:~smooth_compact_carrier K z ->psi (a+h-z)=0 /\ psi (a-z)=0.
  move=>hz.
  have hOutside:r+1<N (z-a).
    rewrite ltNge; apply/negP=>hNear; exact:hz hNear.
  have [hFirst hNext]:=@norm_kernel_source_ball_shift R X N hN a h z r hSmall hOutside.
  split; exact:hOff.
have hFinal:=hError hBound hZero.
apply:(le_lt_trans hFinal).
have hb:b<=`|b| := ler_norm b.
nra.
Qed.
