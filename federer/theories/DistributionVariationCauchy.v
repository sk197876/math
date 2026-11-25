(** Federer (1969), 4.1.5, p. 349: uniform
    approximation with a common compact support yields
    the displayed Cauchy estimate for S(Phi_e*w). The
    proof uses the original finite gauge and scalar
    completeness, without an assumed extension of S. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric FunctionLatticeUP DistributionVariationUP
  DistributionVariationBasic DistributionVariationFinite PositiveNormCauchy PositiveNormLimitUP
  ScalarNormMetricCompleteness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionVariationCauchy.
Variable R:realType.
Variable X:choiceType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable value:Hom E (GRing.Lmodule.clone R (X->Y) _).
Variable S:Hom E R^o.

(** Source for [distribution_variation_approximation_cauchy]:
    the original Cauchy estimate in Federer 4.1.5,
    p. 349. The support and uniform approximation
    premises are the properties proved for the actual
    small-scale compact convolutions. *)
Theorem distribution_variation_approximation_cauchy
    (P:R->E) (w:X->Y) (C:set X) (g:X->R) b r:
  0<r ->function_nonnegative g ->(forall x,C x ->g x= 1) ->
  is_distribution_variation_value NY value S g b%:E ->
  (forall e:R,0<e ->e<r ->forall x,~C x ->value (P e) x=0) ->
  (forall eta:R,0<eta ->exists d:R,0<d /\
    forall e:R,0<e ->e<d ->forall x,NY (value (P e) x-w x)<eta) ->
  positive_norm_cauchy (fun t:R^o=>`|t|) (fun e=>S (P e)).
Proof.
move=>hr hG hOne hGauge hOff hApprox eta hEta.
have hNonnegative:=@distribution_variation_nonnegative R X Y NY hNY E value S g b%:E hG hGauge.
have hb:0<=b by move:hNonnegative; rewrite lee_fin.
have hB:0<b+1 by lra.
have hDen:0<2*(b+1) by rewrite mulr_gt0 // ltr0n.
pose dEta:=eta/(2*(b+1)).
have hDEta:0<dEta by rewrite /dEta divr_gt0.
have[d [hd hUniform]]:=hApprox dEta hDEta.
exists (Num.min r d); split; first by rewrite lt_min hr hd.
move=>e f he heSmall hf hfSmall.
have /andP [her hed]:(e<r)&&(e<d) by rewrite -lt_min.
have /andP [hfr hfd]:(f<r)&&(f<d) by rewrite -lt_min.
have hScaled:0<2*dEta by rewrite mulr_gt0 // ltr0n.
have hPointwise:forall x,NY (value (P e-P f) x)<=(2*dEta)*g x.
  move=>x.
  have hValue:value (P e-P f) x=value (P e) x-value (P f) x:=
    congr1 (fun F:X->Y=>F x) (linearB value (P e) (P f)).
  rewrite hValue.
  case:(pselect (C x))=>hx.
  - rewrite (hOne x hx) mulr1.
    have hDiff:value (P e) x-value (P f) x=
        (value (P e) x-w x)+(w x-value (P f) x) by rewrite addrA subrK.
    rewrite hDiff.
    have hE:=hUniform e he hed x.
    have hF:=hUniform f hf hfd x.
    have hT:=real_seminorm_triangle hNY.1 (value (P e) x-w x) (w x-value (P f) x).
    rewrite (real_seminorm_subtract hNY.1 (w x) (value (P f) x)) in hT.
    lra.
  - rewrite (hOff e he her x hx) (hOff f hf hfr x hx) subrr (real_seminorm_zero hNY.1).
    exact:mulr_ge0 (ltW hScaled) (hG x).
have hBound:=@distribution_variation_finite_scaled_bound R X Y NY hNY E value S g b (2*dEta)
  hGauge hScaled (P e-P f) hPointwise.
rewrite linearB in hBound.
apply:le_lt_trans hBound _.
have hStrict:(2*dEta)*b<(2*dEta)*(b+1) by rewrite ltr_pM2l //; lra.
have hBudget:(2*dEta)*(b+1)=eta.
  have hEq:(2*dEta)*(b+1)=dEta*(2*(b+1)) by ring.
  by rewrite hEq /dEta divfK ?gt_eqF.
by rewrite hBudget in hStrict.
Qed.

(** Source for [distribution_variation_approximation_limit]:
    the original T(w)=lim S(Phi_e*w) exists from
    the displayed Cauchy estimate of Federer 4.1.5,
    p. 349. This is an existence conclusion from
    finite original gauge, not a representation premise. *)
Theorem distribution_variation_approximation_limit
    (P:R->E) (w:X->Y) (C:set X) (g:X->R) b r:
  0<r ->function_nonnegative g ->(forall x,C x ->g x= 1) ->
  is_distribution_variation_value NY value S g b%:E ->
  (forall e:R,0<e ->e<r ->forall x,~C x ->value (P e) x=0) ->
  (forall eta:R,0<eta ->exists d:R,0<d /\
    forall e:R,0<e ->e<d ->forall x,NY (value (P e) x-w x)<eta) ->
  exists t:R,positive_norm_limit (fun a:R^o=>`|a|) (fun e=>S (P e)) t.
Proof.
move=>hr hG hOne hGauge hOff hApprox.
apply:(@positive_norm_cauchy_limit R R^o (fun a:R^o=>`|a|)
  (@scalar_absolute_value_norm R) (@scalar_norm_metric_complete R)).
exact:(@distribution_variation_approximation_cauchy P w C g b r hr hG hOne hGauge hOff hApprox).
Qed.
End DistributionVariationCauchy.
