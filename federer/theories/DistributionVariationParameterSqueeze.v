(** Federer (1969), 4.1.18, p. 375: weak
    convergence supplies the lower scalar-gauge bound;
    the compact-kernel majorant supplies the upper bound.
    Together they give the original weak variation
    limit at every positive small scale.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal lra.
From Federer Require Import Hom ExtendedSupremumUP DistributionVariationUP
  DistributionVariationBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [distribution_variation_finite_near_test]:
    the supremum approximation used for the lower
    weak variation bound of 4.1.18, p. 375,
    from the original scalar-test gauge of 4.1.5,
    p. 349. Empty or infinite gauges are
    not incorrectly assigned a finite witness. *)
Lemma distribution_variation_finite_near_test (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (E:lmodType R)
    (value:Hom E (GRing.Lmodule.clone R (X->Y) _))
    (T:Hom E R^o) (f:X->R) b:
  is_distribution_variation_value NY value T f b%:E ->
  forall eta:R,0<eta ->exists omega:E,
    (forall x,NY (value omega x)<=f x) /\b-eta<T omega.
Proof.
move=>hGauge eta hEta.
apply:contrapT=>hNone.
have hUpper:forall omega:E,
    (forall x,NY (value omega x)<=f x) ->T omega<=b-eta.
  move=>omega hOmega.
  rewrite leNgt;apply/negP=>hGreater.
  apply:hNone;exists omega;by split.
have hSmall:((b:R)%:E<=(b-eta)%:E)%E.
  apply:(extended_supremum_least hGauge)=>a [omega [hOmega <-]].
  rewrite lee_fin;exact:hUpper omega hOmega.
rewrite lee_fin in hSmall;by lra.
Qed.

(** Source for [distribution_variation_parameter_squeeze]:
    the complete lower/upper squeeze for the original
    epsilon-to-zero variation limit in Federer 4.1.18,
    p. 375. No sequence-only weakening or
    finite total variation is assumed. *)
Theorem distribution_variation_parameter_squeeze (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (E:lmodType R)
    (value:Hom E (GRing.Lmodule.clone R (X->Y) _))
    (S:R->Hom E R^o) (T:Hom E R^o) (f:X->R) (G:R->R) b:
  (forall epsilon:R,0<epsilon ->
    is_distribution_variation_value NY value (S epsilon) f (G epsilon)%:E) ->
  is_distribution_variation_value NY value T f b%:E ->
  (forall omega:E,forall eta:R,0<eta ->exists r:R,0<r /\
    forall epsilon:R,0<epsilon ->epsilon<r ->`|S epsilon omega-T omega|<eta) ->
  (forall eta:R,0<eta ->exists r:R,0<r /\
    forall epsilon:R,0<epsilon ->epsilon<r ->G epsilon<=b+eta) ->
  forall eta:R,0<eta ->exists r:R,0<r /\
    forall epsilon:R,0<epsilon ->epsilon<r ->`|G epsilon-b|<eta.
Proof.
move=>hG hT hWeak hUpper eta hEta.
have hQuarter:0<eta/4 by rewrite divr_gt0 // ltr0n.
have hHalf:0<eta/2 by rewrite divr_gt0 // ltr0n.
have [omega [hOmega hNear]]:=distribution_variation_finite_near_test hT hQuarter.
have [r0 [hr0 hBelow]]:=hWeak omega _ hQuarter.
have [r1 [hr1 hAbove]]:=hUpper _ hHalf.
exists (Order.min r0 r1);split;first by rewrite lt_min hr0 hr1.
move=>epsilon he hr.
have hR0:Order.min r0 r1<=r0 by rewrite ge_min lexx.
have hR1:Order.min r0 r1<=r1 by rewrite ge_min lexx orbT.
have hError:=hBelow epsilon he (lt_le_trans hr hR0).
have hHi:=hAbove epsilon he (lt_le_trans hr hR1).
have hLo:=@distribution_variation_upper R X Y NY E value (S epsilon) f
  (G epsilon)%:E (hG epsilon he) omega hOmega.
rewrite lee_fin in hLo.
have hTestLower:T omega-S epsilon omega<eta/4.
  apply:le_lt_trans (ler_norm (T omega-S epsilon omega)) _.
  by rewrite distrC.
rewrite ltr_norml;apply/andP;split;lra.
Qed.
