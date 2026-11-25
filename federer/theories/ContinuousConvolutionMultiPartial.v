(** Federer (1969), 4.1.3, p. 348, using 4.1.2, p. 347: the
    exact multiindex formula for the original convolution.
    The ordered derivative calculation is identified with
    D^alpha by the already proved coordinate formula
    of 3.1.11, p. 223. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses NormRegularity NormClassOneUP
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomials SymmetricExponentWords
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherMultiPartialUP
  NormIteratedDirectionalLaws EuclideanLebesgueDimensions LocallyIntegrableVectorFieldUP
  SmoothingConvolutionUP ContinuousConvolutionIteratedKernel MultiPartialOrderedIdentification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section ContinuousConvolutionMultiPartial.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hR := (@scalar_absolute_value_norm R).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable f:X->Y.
Hypothesis hContinuous:norm_class_zero N NY (fun _=>True) f.
Variable psi:X->R.
Hypothesis hPsi:norm_class_all_orders hN hR (fun _=>True) psi.
Variable r:R.
Hypothesis hOff:forall z,r<N z ->psi z=0.
Variable g:X->Y.
Hypothesis hConvolution:is_smoothing_convolution hNY psi f g.
Local Notation P := (fun j=>@ContinuousMultilinear.space R j X R^o N (fun t:R^o=>`|t|) hN hR).
Local Notation ep := (fun j=>@ContinuousMultilinear.evaluation R j X R^o N (fun t:R^o=>`|t|) hN hR).
Local Notation PN := (fun j=>@ContinuousMultilinear.norm R j X R^o N (fun t:R^o=>`|t|) hN hR).
Local Notation hP := (fun j=>@ContinuousMultilinear.laws R j X R^o N (fun t:R^o=>`|t|) hN hR).
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y N NY hN hNY).
Local Notation ez := (fun j=>@ContinuousMultilinear.evaluation R j X Y N NY hN hNY).
Local Notation ZN := (fun j=>@ContinuousMultilinear.norm R j X Y N NY hN hNY).
Local Notation hZ := (fun j=>@ContinuousMultilinear.laws R j X Y N NY hN hNY).

(** Source for [continuous_convolution_multi_partial_kernel]: the original
    identity D^alpha(Phi*f)=(D^alpha Phi)*f in
    Federer 4.1.2, p. 347. The supplied
    derivative fields satisfy the exact derivative graph,
    whose existence follows separately from smoothness. *)
Theorem continuous_convolution_multi_partial_kernel k (alpha:symmetric_indices n k) (theta:X->R) (q:X->Y):
  (forall a,has_norm_multi_partial N ep PN (fun _=>True) psi alpha a (theta a)) ->
  (forall a,has_norm_multi_partial N ez ZN (fun _=>True) g alpha a (q a)) ->
  is_smoothing_convolution hNY theta f q.
Proof.
move=>hTheta hQ.
pose nu:=symmetric_monomial_word idfun (symmetric_indices_unbound alpha).
have hSize:size nu=k by rewrite /nu symmetric_monomial_word_size symmetric_indices_unbound_degree.
have hCount i:count_mem i nu=symmetric_indices_unbound alpha i.
  have h:=congr1 (fun a:symmetric_multi_index n=>a i) (symmetric_exponent_word_count_monomial (symmetric_indices_unbound alpha)).
  by rewrite /symmetric_exponent_word_count ffunE in h.
have [theta' [q' [_ [_ [hConv [hIterTheta hIterQ]]]]]]:=
  @continuous_smooth_convolution_iterated_kernel R n Y NY hNY hY f hContinuous
    psi hPsi r hOff g hConvolution [seq (@coordinate_basis R n) i|i<-nu].
have hSameTheta:theta=theta'.
  apply:funext=>a.
  have hIter:=@norm_multi_partial_to_ordered R n R^o (fun t:R^o=>`|t|) hR P ep PN hP
    (fun _=>True) psi k alpha nu a (theta a) hSize hCount (hTheta a).
  exact:(norm_iterated_directional_unique hR hIter (hIterTheta a)).
have hSameQ:q=q'.
  apply:funext=>a.
  have hIter:=@norm_multi_partial_to_ordered R n Y NY hNY Z ez ZN hZ
    (fun _=>True) g k alpha nu a (q a) hSize hCount (hQ a).
  exact:(norm_iterated_directional_unique hNY hIter (hIterQ a)).
by rewrite -hSameTheta -hSameQ in hConv.
Qed.
End ContinuousConvolutionMultiPartial.
