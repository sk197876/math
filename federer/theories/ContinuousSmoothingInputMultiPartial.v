(** Federer (1969), 4.1.3, p. 348, using 4.1.2, p. 347: the
    original multiindex derivatives of a class-i input
    commute with smoothing. All ordered derivative
    identities are identified with the exact symmetric
    differential by the original 3.1.11 coordinate formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses NormRegularity
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomials SymmetricExponentWords
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherMultiPartialUP NormIteratedDirectionalLaws
  SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP ContinuousSmoothingInputIteration MultiPartialOrderedIdentification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section ContinuousSmoothingInputMultiPartial.
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
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y N NY hN hNY).
Local Notation ez := (fun j=>@ContinuousMultilinear.evaluation R j X Y N NY hN hNY).
Local Notation ZN := (fun j=>@ContinuousMultilinear.norm R j X Y N NY hN hNY).
Local Notation hZ := (fun j=>@ContinuousMultilinear.laws R j X Y N NY hN hNY).

(** Source for [continuous_smoothing_input_multi_partial]: the original
    identity D^alpha(Phi*f)=Phi*D^alpha f for
    class-i input and |alpha|=i,
    Federer 4.1.2, p. 347. Both
    fields have their exact actual multiindex derivative graphs. *)
Theorem continuous_smoothing_input_multi_partial k (alpha:symmetric_indices n k)
    (f g theta q:X->Y):
  norm_class hN hNY (fun _=>True) f k ->
  is_smoothing_convolution hNY (family e) f g ->
  (forall a,has_norm_multi_partial N ez ZN (fun _=>True) f alpha a (theta a)) ->
  (forall a,has_norm_multi_partial N ez ZN (fun _=>True) g alpha a (q a)) ->
  is_smoothing_convolution hNY (family e) theta q.
Proof.
move=>hClass hConv hTheta hQ.
pose nu:=symmetric_monomial_word idfun (symmetric_indices_unbound alpha).
have hSize:size nu=k by rewrite /nu symmetric_monomial_word_size symmetric_indices_unbound_degree.
have hCount i:count_mem i nu=symmetric_indices_unbound alpha i.
  have h:=congr1 (fun a:symmetric_multi_index n=>a i)
    (symmetric_exponent_word_count_monomial (symmetric_indices_unbound alpha)).
  by rewrite /symmetric_exponent_word_count ffunE in h.
pose s:=[seq (@coordinate_basis R n) i|i<-nu].
have hDegree:(size s+0)%N=k by rewrite /s addn0 size_map hSize.
have hInput:norm_class hN hNY (fun _=>True) f (size s+0)%N by rewrite hDegree.
have [theta' [q' [_ [hConv' [hIterTheta hIterQ]]]]]:=
  @continuous_smoothing_input_iterated_class R n Y NY hNY hY phi hPhi family hFamily e he s 0%N f g hInput hConv.
have hSameTheta:theta=theta'.
  apply:funext=>a.
  have hIter:=@norm_multi_partial_to_ordered R n Y NY hNY Z ez ZN hZ
    (fun _=>True) f k alpha nu a (theta a) hSize hCount (hTheta a).
  exact:(norm_iterated_directional_unique hNY hIter (hIterTheta a)).
have hSameQ:q=q'.
  apply:funext=>a.
  have hIter:=@norm_multi_partial_to_ordered R n Y NY hNY Z ez ZN hZ
    (fun _=>True) g k alpha nu a (q a) hSize hCount (hQ a).
  exact:(norm_iterated_directional_unique hNY hIter (hIterQ a)).
by rewrite -hSameTheta -hSameQ in hConv'.
Qed.
End ContinuousSmoothingInputMultiPartial.
