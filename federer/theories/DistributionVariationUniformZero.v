(** Federer (1969), 4.1.5, pp. 349–350: the
    finite original gauge makes uniformly vanishing tests
    with common compact support tend to zero under S.
    This is the comparison estimate behind independence
    and linearity of the convolution extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric FunctionLatticeUP DistributionVariationUP
  DistributionVariationBasic DistributionVariationFinite PositiveNormLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [distribution_variation_uniform_zero_limit]:
    the zero-limit version of the finite-gauge estimate
    in Federer 4.1.5, p. 349. The original scalar
    majorant equals one on the common compact support. *)
Theorem distribution_variation_uniform_zero_limit (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) (E:lmodType R)
    (value:Hom E (GRing.Lmodule.clone R (X->Y) _)) (S:Hom E R^o)
    (P:R->E) (C:set X) (g:X->R) b r:
  0<r ->function_nonnegative g ->(forall x,C x ->g x= 1) ->
  is_distribution_variation_value NY value S g b%:E ->
  (forall e:R,0<e ->e<r ->forall x,~C x ->value (P e) x=0) ->
  (forall eta:R,0<eta ->exists d:R,0<d /\
    forall e:R,0<e ->e<d ->forall x,NY (value (P e) x)<eta) ->
  positive_norm_limit (fun a:R^o=>`|a|) (fun e=>S (P e)) 0.
Proof.
move=>hr hG hOne hGauge hOff hApprox eta hEta.
have hNonnegative:=@distribution_variation_nonnegative R X Y NY hNY E value S g b%:E hG hGauge.
have hb:0<=b by move:hNonnegative; rewrite lee_fin.
have hB:0<b+1 by lra.
pose dEta:=eta/(b+1).
have hDEta:0<dEta by rewrite /dEta divr_gt0.
have[d [hd hUniform]]:=hApprox dEta hDEta.
exists (Num.min r d); split; first by rewrite lt_min hr hd.
move=>e he hSmall.
have /andP [her hed]:(e<r)&&(e<d) by rewrite -lt_min.
have hPointwise:forall x,NY (value (P e) x)<=dEta*g x.
  move=>x; case:(pselect (C x))=>hx.
  - rewrite (hOne x hx) mulr1; exact:ltW (hUniform e he hed x).
  - rewrite (hOff e he her x hx) (real_seminorm_zero hNY.1).
    exact:mulr_ge0 (ltW hDEta) (hG x).
have hBound:=@distribution_variation_finite_scaled_bound R X Y NY hNY E value S g b dEta
  hGauge hDEta (P e) hPointwise.
rewrite subr0; apply:le_lt_trans hBound _.
have hStrict:dEta*b<dEta*(b+1) by rewrite ltr_pM2l //; lra.
by rewrite /dEta divfK ?gt_eqF // in hStrict.
Qed.
