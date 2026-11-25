(** Federer (1969), 4.1.14, p. 372, final sentence:
    for a class-one map the actual smooth differentials converge
    uniformly on compact sets. The proof uses exactly the finite-class
    smoothing assertion of 4.1.2, p. 347, and the original norm
    identification D^1 f=Df in 3.1.11, p. 219. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness SmoothCompactSet ContinuousMultilinearUP
  ContinuousMultilinearNorm ContinuousMultilinearSealed ContinuousMultilinearOne
  ContinuousOperatorUP NormOperatorNormUP NormHigherDifferentialUP NormHigherDifferentialFirst
  SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP
  EuclideanOwnNormCompleteness EuclideanOwnNormSeparable EuclideanHomOperator
  HomSpaceTopology CurrentMapDifferential FiniteClassSmoothingHigherUniform.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ClassOneSmoothingDifferentialUniform.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation Z:=(fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation ev:=(fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation ZN:=(fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hZ:=(fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
Local Notation Op:=(@euclidean_operator_norm R n nu).
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable f:X->Y.
Variable g:R->X->Y.
Hypothesis hConvolution:forall e:R,0<e->is_smoothing_convolution hNY (family e) f (g e).
Arguments hConvolution : clear implicits.

(** Source for [class_one_smoothing_differential_uniform]: the
    original class-one hypothesis suffices for uniform convergence
    of the actual Dg_e to Df on K, supporting Federer 4.1.14,
    p. 372. The spaces, dimensions and degree-zero norm convention
    are unchanged, and no whole-operator separability is required. *)
Theorem class_one_smoothing_differential_uniform:
  norm_class_one NX NY (fun _=>True) f ->
  forall (K:smooth_compact_set hNX (fun _=>True)) (eta:R),0<eta->
    exists d:R,0<d /\ forall e:R,0<e->e<d->forall a,
      smooth_compact_carrier K a->
      Op (@current_map_differential R n nu (fun _=>True) (g e) a-
        @current_map_differential R n nu (fun _=>True) f a)<eta.
Proof.
move=>hClass K eta hEta.
have hFinite:norm_class hNX hNY (fun _=>True) f 1%N:=
  (@norm_class_firstP R X Y NX NY hNX hNY (fun _=>True) f).2 hClass.
have[DF [DG [hDF [hDFContinuous [hDG hUniform]]]]]:=
  @finite_class_smoothing_higher_uniform R n Y NY hNY
    (@euclidean_own_norm_complete R nu) (@euclidean_own_norm_separable R nu)
    phi hPhi family hFamily f g hConvolution 1%N hFinite.
pose J:=@continuous_multilinear_one_evaluation R X Y (Z 1%N) NX NY
  (@ev 1%N) (@ZN 1%N) (hZ 1%N).
have hActualF:forall a,@current_map_differential R n nu (fun _=>True) f a=J (DF a).
  move=>a;apply:current_map_differential_unique.
  exact:((@norm_higher_differential_first R X Y NX NY hNX hNY Z ev ZN hZ
    (fun _=>True) f a (DF a)).1 (hDF a)).
have hActualG:forall e:R,0<e->forall a,
    @current_map_differential R n nu (fun _=>True) (g e) a=J (DG e a).
  move=>e he a;apply:current_map_differential_unique.
  exact:((@norm_higher_differential_first R X Y NX NY hNX hNY Z ev ZN hZ
    (fun _=>True) (g e) a (DG e a)).1 (hDG e he a)).
have hNormBound:forall z:Z 1%N,Op (J z)<=@ZN 1%N z.
  move=>z.
  have hNorm:=@continuous_multilinear_one_norm_laws R X Y (Z 1%N) NX NY
    (@ev 1%N) (@ZN 1%N) (hZ 1%N) z.
  apply:hom_operator_norm_least.
  - exact:norm_operator_nonnegative hNorm.
  - exact:norm_operator_bound hNorm.
have[d [hd hNear]]:=hUniform K eta hEta.
exists d;split;first exact:hd.
move=>e he hSmall a ha.
rewrite (hActualG e he a) (hActualF a) -linearB.
exact:(le_lt_trans (hNormBound (DG e a-DF a)) (hNear e he hSmall a ha)).
Qed.
End ClassOneSmoothingDifferentialUniform.
