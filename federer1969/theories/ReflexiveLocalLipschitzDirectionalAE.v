(** Federer (1969), 4.1.2, p. 347: actual directional
    derivatives exist almost everywhere for Lipschitz inputs into
    a separable reflexive Banach space. The original curve theorem
    2.9.22 and the proved Borel-domain Fubini transfer supply them. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets cardinality reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormMetricScaleContinuity NormedCurveDerivativeUP NormDirectionalQuotientContinuity
  ContinuousDualUP ContinuousDualNorm ContinuousBidualUP SeparableReflexiveLipschitzDifferentiation
  EuclideanLebesgueDimensions EuclideanDirectionalNullSlices RealMetricBackground LebesgueScalarMeasure
  MeasureAlmostUP MeasureAlmostBasic TopologicalBorel LipschitzUP
  EuclideanLocalLipschitzRepresentative ReflexiveLipschitzDirectionalAE.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ReflexiveLocalLipschitzDirectionalAE.
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

Hypothesis hLocal:is_locally_metric_lipschitz setT
  (f:real_norm_metric_space hN->real_norm_metric_space hNY).

(** Source for [reflexive_local_lipschitz_directional_ae]: actual
    two-sided norm derivatives exist almost everywhere for the full
    locally Lipschitz, separable reflexive Banach input of
    Federer 4.1.2, p. 347. Countably many compact-ball
    representatives preserve the original derivatives locally. *)
Theorem reflexive_local_lipschitz_directional_ae v:
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set x|exists w:Y,punctured_norm_limit NY
      (fun t=>t^-1*:(f (x+t*:v)-f x)) w].
Proof.
have hFor m:exists p:((X->Y)*R)%type,0<p.2 /\
    (forall x y,NY (p.1 x-p.1 y)<=p.2*N (x-y)) /\
    (forall x,N x<=(m.+1)%:R ->p.1 x=f x).
  have hR:0<((m.+1)%:R:R) by rewrite ltr0n.
  have[g [L [hL [hLip hEq]]]]:=@euclidean_local_lipschitz_representative_exists R n Y NY hNY f hLocal
    ((m.+1)%:R:R) (ltW hR).
  by exists (g,L); split=>//; split.
have[F hF]:=choice hFor.
pose P m:set X:=[set x|exists w:Y,punctured_norm_limit NY
  (fun t=>t^-1*:((F m).1 (x+t*:v)-(F m).1 x)) w].
have hAE m:measure_almost_everywhere (@euclidean_lebesgue_measure R n) (P m).
  exact:(@reflexive_lipschitz_directional_ae R n Y YD YB NY hNY hY hSep
    ed DN hYD eb BN hYB tau hTau hReflexive (F m).1 (F m).2
    (ltW (hF m).1) (hF m).2.1 v).
have hAll:=@measure_almost_everywhere_countable R X nat (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) setT P (countableP setT) (fun m _=>hAE m).
apply:(@measure_almost_everywhere_mono R X (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) _ _ _ hAll).
move=>x hx.
pose m:=Num.bound (N x).
have hBound:N x<m%:R by apply:archi_boundP; exact:real_seminorm_nonnegative hN.1 x.
have hR:N x<(m.+1)%:R.
  apply:lt_le_trans hBound _; by rewrite ler_nat.
have[w hw]:=hx m Logic.I.
have hNv:=real_seminorm_nonnegative hN.1 v.
have hDen:0<N v+1 by lra.
have hGap:0<(m.+1)%:R-N x by rewrite subr_gt0.
pose r:=((m.+1)%:R-N x)/(N v+1).
have hr:0<r by rewrite /r divr_gt0.
have hNear t:`|t|<r ->(F m).1 (x+t*:v)=f (x+t*:v).
  move=>ht; apply:(hF m).2.2.
  have hProduct:`|t|*(N v+1)<(m.+1)%:R-N x.
    by move:ht; rewrite /r ltr_pdivlMr.
  rewrite mulrDr mulr1 in hProduct.
  have hTriangle:=real_seminorm_triangle hN.1 x (t*:v).
  rewrite (real_seminorm_scale hN.1) in hTriangle.
  have hAbs:=normr_ge0 t.
  have hSmall:N x+`|t|*N v<(m.+1)%:R by lra.
  exact:le_trans hTriangle (ltW hSmall).
have hBase:(F m).1 x=f x.
  have hZero: `|(0:R)|<r by rewrite normr0.
  have h:=hNear 0 hZero; by rewrite scale0r addr0 in h.
exists w=>eta hEta.
have[d [hd hLimit]]:=hw eta hEta.
exists (Num.min r d); split; first by rewrite lt_min hr hd.
move=>t /andP[ht0 ht].
have /andP[htr htd]:(`|t|<r)&&(`|t|<d) by rewrite -lt_min.
rewrite -(hNear t htr) -hBase.
apply:hLimit; by apply/andP.
Qed.
End ReflexiveLocalLipschitzDirectionalAE.
