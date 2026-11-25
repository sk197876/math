(** Federer (1969), 4.1.2, p. 347: actual directional
    derivatives exist almost everywhere for Lipschitz inputs into
    a separable reflexive Banach space. The original curve theorem
    2.9.22 and the proved Borel-domain Fubini transfer supply them. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormMetricScaleContinuity NormedCurveDerivativeUP NormDirectionalQuotientContinuity
  ContinuousDualUP ContinuousDualNorm ContinuousBidualUP SeparableReflexiveLipschitzDifferentiation
  EuclideanLebesgueDimensions EuclideanDirectionalNullSlices RealMetricBackground LebesgueScalarMeasure
  MeasureAlmostUP MeasureAlmostBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ReflexiveLipschitzDirectionalAE.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y YD YB:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Hypothesis hSep:is_separable_normed_space hNY.
Variable ed:Hom YD (Hom Y R^o).
Variable DN:YD->R.
Hypothesis hYD:is_continuous_dual hNY ed DN.
Variable eb:Hom YB (Hom YD R^o).
Variable BN:YB->R.
Hypothesis hYB:is_continuous_dual (continuous_dual_norm_is_norm hYD) eb BN.
Variable tau:Hom Y YB.
Hypothesis hTau:is_bidual_embedding ed eb tau.
Hypothesis hReflexive:is_reflexive_embedding tau.
Variable f:X->Y.
Variable L:R.
Hypothesis hL:0<=L.
Hypothesis hLip:forall x y,NY (f x-f y)<=L*N (x-y).

(** Source for [reflexive_lipschitz_directional_ae]: actual two-sided
    norm derivatives in the reflexive input clause of Federer 4.1.2,
    p. 347. This intermediate global Lipschitz theorem has
    no finite-dimensional restriction on the Banach target. *)
Theorem reflexive_lipschitz_directional_ae v:
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set x|exists w:Y,punctured_norm_limit NY
      (fun t=>t^-1*:(f (x+t*:v)-f x)) w].
Proof.
pose P:set X:=[set x|exists w:Y,punctured_norm_limit NY
  (fun t=>t^-1*:(f (x+t*:v)-f x)) w].
have hF:continuous (f:real_norm_metric_space hN->real_norm_metric_space hNY).
  exact:(@metric_fixed_lipschitz_continuous R (real_norm_metric_space hN)
    (real_norm_metric_space hNY) f L hL hLip).
have hP:=@norm_directional_derivative_domain_borel R X Y N NY hN hNY hY f v hF.
change (euclidean_lebesgue_measure n (~` P)=0%E).
apply:(@euclidean_directional_null_slices R n v (~` P) (borel_set_complement hP)).
move=>x.
have[C [hCc hCd]]:=hSep.
have hLine s t:NY (f (x+s*:v)-f (x+t*:v))<=(L*N v)*`|s-t|.
  have h:=hLip (x+s*:v) (x+t*:v).
  have hDiff:x+s*:v-(x+t*:v)=(s-t)*:v.
    by rewrite opprD addrACA subrr add0r -scalerBl.
  by rewrite hDiff (real_seminorm_scale hN.1) mulrA mulrAC in h.
have hBound:0<=L*N v:=mulr_ge0 hL (real_seminorm_nonnegative hN.1 v).
have hAE:=@separable_reflexive_lipschitz_derivative_ae R Y YD YB NY hNY
  ed DN hYD eb BN hYB tau (fun t=>f (x+t*:v)) (L*N v) C
  hTau hReflexive hCc hCd hBound hLine.
change (measure_almost_everywhere (@lebesgue_scalar_measure R) [set t:R|P (x+t*:v)]).
apply:(@measure_almost_everywhere_mono R R (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ hAE).
move=>t [w [hw _]]; exists w.
have hShift:(fun h:R=>h^-1*:(f (x+(t+h)*:v)-f (x+t*:v)))=
    (fun h=>h^-1*:(f ((x+t*:v)+h*:v)-f (x+t*:v))).
  apply:funext=>h; by rewrite scalerDl addrA.
change (punctured_norm_limit NY
  (fun h:R=>h^-1*:(f (x+(t+h)*:v)-f (x+t*:v))) w) in hw.
by rewrite hShift in hw.
Qed.
End ReflexiveLipschitzDirectionalAE.
