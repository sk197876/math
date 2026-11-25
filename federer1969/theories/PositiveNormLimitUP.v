(** Federer (1969), 4.1.4, p. 349: limits of the
    smoothed scalar evaluations as epsilon decreases to zero.
    The independent positive-parameter norm limit is related
    to the earlier two-sided punctured limit before it is used. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_norm_limit]: the original epsilon
    tends to zero from above convention in both displayed
    limits of Federer 4.1.4, p. 349. *)
Definition positive_norm_limit (R:realType) (Y:lmodType R)
    (NY:Y->R) (f:R->Y) (a:Y):Prop:=
  forall eta:R,0<eta ->exists d:R,0<d /\
    forall e:R,0<e ->e<d ->NY (f e-a)<eta.

(** Source for [positive_norm_limit_unique]: uniqueness of
    the original scalar limit used to identify the small-scale
    constants in Federer 4.1.4, p. 349. The earlier norm-limit
    uniqueness theorem gives the general normed-target version. *)
Lemma positive_norm_limit_unique (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (f:R->Y) a b:
  positive_norm_limit NY f a ->positive_norm_limit NY f b ->a=b.
Proof.
move=>ha hb.
have hAbs c:positive_norm_limit NY f c ->
    punctured_norm_limit NY (fun t=>f `|t|) c.
  move=>hc eta hEta; have[d [hd hBound]]:=hc eta hEta.
  exists d; split=>// t /andP [ht htd]; exact:(hBound `|t| ht htd).
exact:(punctured_norm_limit_unique hNY (hAbs a ha) (hAbs b hb)).
Qed.

(** Source for [positive_norm_limit_eventual_equality]: eventually
    identical scalar evaluations have the same original positive
    limit, supporting both limits in Federer 4.1.4, p. 349. *)
Lemma positive_norm_limit_eventual_equality (R:realType) (Y:lmodType R)
    (NY:Y->R) (f g:R->Y) a:
  (exists r:R,0<r /\ forall e:R,0<e ->e<r ->f e=g e) ->
  positive_norm_limit NY f a ->positive_norm_limit NY g a.
Proof.
move=>[r [hr hEq]] hf eta hEta.
have[d [hd hBound]]:=hf eta hEta.
exists (Num.min r d); split; first by rewrite lt_min hr hd.
move=>e he hSmall.
have /andP [her hed]:(e<r)&&(e<d) by move:hSmall; rewrite lt_min.
rewrite -(@hEq e he her); exact:(hBound e he hed).
Qed.

(** Source for [positive_norm_limit_constant]: the constant
    evaluation case used in the final limit inference of
    Federer 4.1.4, p. 349. *)
Lemma positive_norm_limit_constant (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (a:Y):
  positive_norm_limit NY (fun _=>a) a.
Proof.
move=>eta hEta; exists 1; split; first exact:ltr01.
by move=>e _ _; rewrite subrr (real_seminorm_zero hNY.1).
Qed.
