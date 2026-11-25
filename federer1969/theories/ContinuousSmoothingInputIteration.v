(** Federer (1969), 4.1.3, p. 348, using 4.1.2, p. 347: for
    a class-i input, every ordered derivative through
    degree i commutes with the original smoothing.
    The proof iterates the checked class-one formula
    and the original derivative class-loss law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses NormClassOneUP NormRegularity
  NormDifferentialUP NormDifferentialDirectional NormedCurveDerivativeUP NormIteratedDirectionalUP NormIteratedDirectionalLaws
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanLebesgueDimensions
  LocallyIntegrableVectorFieldUP ContinuousFieldLocalIntegrability SmoothingKernelUP SmoothingDilationUP
  SmoothingConvolutionUP ContinuousCompactConvolution SmoothingDilationSmooth SmoothingDilationNonzeroRadius ContinuousSmoothingInputDirectional NormDirectionalClassLoss.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ContinuousSmoothingInputIteration.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable e:R.
Hypothesis he:0<e.

(** Source for [continuous_smoothing_input_iterated_class]: the original
    iterated identity D^i(Phi*f)=Phi*D^i f
    for class-i inputs, Federer 4.1.2, p. 347,
    with an arbitrary residual class k and
    exact recursively defined derivative graphs retained. *)
Theorem continuous_smoothing_input_iterated_class (s:seq X):
  forall k (f g:X->Y),norm_class hN hNY (fun _=>True) f (size s+k)%N ->
    is_smoothing_convolution hNY (family e) f g ->
    exists (theta q:X->Y),
      norm_class hN hNY (fun _=>True) theta k /\
      is_smoothing_convolution hNY (family e) theta q /\
      (forall a,has_norm_iterated_directional NY (fun _=>True) f s a (theta a)) /\
      (forall a,has_norm_iterated_directional NY (fun _=>True) g s a (q a)).
Proof.
elim:s=>[|v s IH] k f g hF hConv.
- exists f,g; split; first exact hF.
  split=>//; split; by move=>a; split.
- have hDegree:(size s+k.+1)%N=(size (v::s)+k)%N by rewrite /= addnS addSn.
  have hF':norm_class hN hNY (fun _=>True) f (size s+k.+1)%N by rewrite hDegree.
  have [theta [q [hTheta [hQ [hIterTheta hIterQ]]]]]:=@IH k.+1 f g hF' hConv.
  have h1:(1<=k.+1)%N by [].
  have hTheta1:norm_class hN hNY (fun _=>True) theta 1%N.
    exact:(norm_class_lower h1 hTheta).
  have [D hD]:=(@norm_class_firstP R X Y N NY hN hNY (fun _=>True) theta).1 hTheta1.
  have hActual a:has_norm_differential N NY (fun _=>True) theta a (D a).
    exact:(norm_class_one_differential hD Logic.I).
  pose xi:=fun a=>D a v.
  have hXiClass:=@norm_directional_class_loss R X Y N NY hN hNY theta D v k hTheta hActual.
  have hXiLocal:=@continuous_field_locally_norm_integrable R n Y NY hNY xi
    (norm_class_continuous hXiClass).
  have [q' hQ']:=@continuous_compact_convolution_exists R n Y NY hNY hY xi
    (norm_class_continuous hXiClass) (family e)
    (@smoothing_dilation_smooth R n phi hPhi family hFamily e he) e
    (@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he).
  exists xi,q'; split; first exact hXiClass.
  split=>//; split=>a.
  + exists theta; split.
    * move=>x y hy; exact:(@norm_iterated_directional_unique R X Y NY hNY
        (fun _=>True) f s x (theta x) y (hIterTheta x) hy).
    * split.
      - exists 1; split; first exact:ltr01.
        move=>t _; exists (theta (a+t*:v)); exact:hIterTheta.
      - exact:(norm_differential_directional_limit hN hNY (hActual a) v).
  + exists q; split.
    * move=>x y hy; exact:(@norm_iterated_directional_unique R X Y NY hNY
        (fun _=>True) g s x (q x) y (hIterQ x) hy).
    * split.
      - exists 1; split; first exact:ltr01.
        move=>t _; exists (q (a+t*:v)); exact:hIterQ.
      - exact:(@continuous_smoothing_input_directional_derivative R n Y NY hNY
          phi hPhi family hFamily e he theta xi q q' hTheta1 D hActual v (fun _=>erefl)
          hQ hQ' a).
Qed.
End ContinuousSmoothingInputIteration.
