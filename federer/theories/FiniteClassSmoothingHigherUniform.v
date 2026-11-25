(** Federer (1969), 4.1.2, p. 347, used in the class-one
    conclusion of 4.1.14, p. 372: smoothing a class-k map
    converges in its kth differential uniformly on compact sets.
    The finite original class is retained. A fixed input differential
    field and uniqueness remove any scale-dependent choices before
    applying the registered continuous-range smoothing theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  NormClassOneUP NormRegularity NormClassHigherUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearSealed
  ContinuousMultilinearBanach NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherDifferentialSealed PartialFunctionExtensionSealed SmoothCompactSet
  SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP
  SmoothingInputHigherDifferential ContinuousSmoothingLocallyUniform.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section FiniteClassSmoothingHigherUniform.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Hypothesis hSep:is_separable_normed_space hNY.
Local Notation Z:=(fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation ev:=(fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation ZN:=(fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hZ:=(fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable f:X->Y.
Variable g:R->X->Y.
Hypothesis hConvolution:forall e:R,0<e->is_smoothing_convolution hNY (family e) f (g e).
Arguments hConvolution : clear implicits.

(** Source for [finite_class_smoothing_higher_uniform]: the
    finite-class differential commutation and local uniform convergence
    in Federer 4.1.2, p. 347. The case k=1 supports 4.1.14,
    p. 372. No higher regularity or whole-operator separability
    premise is introduced. All displayed differential fields are actual. *)
Theorem finite_class_smoothing_higher_uniform k:
  norm_class hNX hNY (fun _=>True) f k ->
  exists DF:X->Z k,exists DG:R->X->Z k,
    (forall a,has_norm_higher_differential NX ev ZN (fun _=>True) f k a (DF a)) /\
    norm_class_zero NX (@ZN k) (fun _=>True) DF /\
    (forall e:R,0<e->forall a,
      has_norm_higher_differential NX ev ZN (fun _=>True) (g e) k a (DG e a)) /\
    forall (K:smooth_compact_set hNX (fun _=>True)) (eta:R),0<eta->
      exists d:R,0<d /\ forall e:R,0<e->e<d->forall a,
        smooth_compact_carrier K a->@ZN k (DG e a-DF a)<eta.
Proof.
move=>hClass.
have[_ [DF [hDF hDFContinuous]]]:=hClass.
pose DG (e:R) (a:X):Z k:=@PartialFunctionExtension.value X (Z k)
  (@NormHigherDifferential.value R X Y NX NY hNX hNY Z ev ZN hZ
    (fun _=>True) (g e) k) 0 a.
have hPair e (he:0<e):
    (forall a,has_norm_higher_differential NX ev ZN (fun _=>True) (g e) k a (DG e a)) /\
    is_smoothing_convolution (continuous_multilinear_norm_is_norm hNY (hZ k))
      (family e) DF (DG e).
  have[DF' [DG' [hDF' [hDG' hConv]]]]:=@smoothing_input_higher_differential_exists
    R n Y NY hNY hY hSep phi hPhi family hFamily e he k f (g e) hClass (hConvolution e he).
  have hInput:DF'=DF.
    apply:funext=>a.
    exact:(@norm_higher_differential_unique R X Y NX NY hNX hNY Z ev ZN hZ
      (fun _=>True) f k a (DF' a) (DF a) (hDF' a) (hDF a Logic.I)).
  have hOutput:DG'=DG e.
    apply:funext=>a;symmetry.
    exact:(@PartialFunctionExtension.laws X (Z k)
      (@NormHigherDifferential.value R X Y NX NY hNX hNY Z ev ZN hZ
        (fun _=>True) (g e) k) 0 a (DG' a)
      ((@NormHigherDifferential.laws R X Y NX NY hNX hNY Z ev ZN hZ
        (fun _=>True) (g e) k a (DG' a)).2 (hDG' a))).
  rewrite hInput hOutput in hConv.
  split;last exact:hConv.
  by move=>a;rewrite -hOutput;exact:hDG' a.
exists DF,DG;split;first by move=>a;exact:hDF a Logic.I.
split;first exact:hDFContinuous.
split;first by move=>e he;exact:(hPair e he).1.
move=>K eta hEta.
exact:(@continuous_smoothing_locally_uniform R n (Z k) (@ZN k)
  (continuous_multilinear_norm_is_norm hNY (hZ k))
  (@continuous_multilinear_complete_general R k X Y (Z k) NX NY hNX hNY
    (@ev k) (@ZN k) (hZ k) hY)
  phi hPhi family hFamily DF DG (fun e he=>(hPair e he).2) hDFContinuous K eta hEta).
Qed.
End FiniteClassSmoothingHigherUniform.
