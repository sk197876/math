(** Federer (1969), 4.1.2, p. 347: the original directional
    derivative of a Lipschitz field has a measurable bounded total
    representative on its conull domain. Its values on every point
    of the original derivative graph are preserved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormedCurveDerivativeUP NormedDerivativeBounds NormDirectionalQuotientContinuity
  NormClassZeroWhole NormClassZeroTotalMeasurable PuncturedNormReciprocalSequence
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  PartialFunctionUP PartialFunctionBasic PartialFunctionLimitUP MeasurableFunctionUP MeasurablePartialLimits
  MeasureAlmostUP MeasureAlmostBasic NormDirectionalMeasurableRepresentative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NormDirectionalBoundedRepresentative.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable f:X->Y.
Variable L:R.
Hypothesis hL:0<=L.
Hypothesis hLip:forall x y,NY (f x-f y)<=L*N (x-y).
Variable v:X.
Local Notation Der := (fun x w=>punctured_norm_limit NY
  (fun t=>t^-1*:(f (x+t*:v)-f x)) w).

(** Source for [norm_directional_derivative_lipschitz_bound]: the
    original finite Lipschitz bound controls every actual D_v f,
    supporting the reflexive input clause of Federer 4.1.2, p. 347. *)
Lemma norm_directional_derivative_lipschitz_bound x w:
  Der x w ->NY w<=L*N v.
Proof.
move=>hDer.
have hLine s t:NY (f (x+s*:v)-f (x+t*:v))<=(L*N v)*`|s-t|.
  have h:=hLip (x+s*:v) (x+t*:v).
  have hDiff:x+s*:v-(x+t*:v)=(s-t)*:v.
    by rewrite opprD addrACA subrr add0r -scalerBl.
  by rewrite hDiff (real_seminorm_scale hN.1) mulrA mulrAC in h.
have hCurve:has_normed_curve_derivative NY (fun t=>f (x+t*:v)) 0 w.
  move=>eta hEta; have[d [hd hBound]]:=hDer eta hEta.
  exists d; split=>//t ht.
  by rewrite add0r scale0r addr0; exact:hBound t ht.
exact:(@normed_curve_derivative_lipschitz_bound R Y NY hNY (fun t=>f (x+t*:v))
  (L*N v) 0 w hLine hCurve).
Qed.

Hypothesis hF:continuous (f:real_norm_metric_space hN->real_norm_metric_space hNY).
Hypothesis hExists:measure_almost_everywhere mu [set x|exists w,Der x w].

(** Source for [norm_directional_bounded_representative_exists]:
    an actual bounded measurable representative of D_v f,
    preserving the entire original partial graph and zero off its
    domain, Federer 4.1.2, p. 347. The conull derivative premise
    is separately proved for reflexive Banach inputs. *)
Theorem norm_directional_bounded_representative_exists:
  exists xi:X->Y,
    (forall x w,Der x w ->xi x=w) /\
    (forall x,~(exists w,Der x w) ->xi x=0) /\
    (forall x,NY (xi x)<=L*N v) /\
    is_measure_measurable_function mu
      (partial_function_total (fun x=>(xi x:real_norm_metric_space hNY))) /\
    measure_almost_everywhere mu [set x|Der x (xi x)].
Proof.
have[xi [hRep [hZero [hMeas hAE]]]]:=@norm_directional_measurable_representative_exists
  R n Y NY hNY f v hF hExists.
exists xi; split; first exact hRep.
split; first exact hZero.
split.
- move=>x; case:(pselect (exists w,Der x w))=>[[w hw]|hn].
  + rewrite (hRep x w hw); exact:norm_directional_derivative_lipschitz_bound hw.
  + rewrite (hZero x hn) (real_seminorm_zero hNY.1).
    exact:mulr_ge0 hL (real_seminorm_nonnegative hN.1 v).
- by split.
Qed.
End NormDirectionalBoundedRepresentative.
