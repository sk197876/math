(** Federer (1969), 3.4.7, p. 325: the
    actual transverse pullback is a ring monomorphism.
    This supporting germ argument uses an actual analytic
    section and its inverse equations on neighbourhoods. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormOpenPreimage NormRegularity NormAnalyticUP NormAnalyticLocal
  AnalyticGermNeighbourhood LocalGermUP LocalGermSealed AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermRingLaws AnalyticGermRing AnalyticPullbackRepresentative AnalyticPullbackSealed
  AnalyticPullbackRingMorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_ring_pullback_injective_section]:
    the monomorphism assertion used in 3.4.7,
    p. 325. An actual analytic section through
    the original centre detects equality of germs;
    no injectivity conclusion is a premise. *)
Theorem analytic_ring_pullback_injective_section (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (B:set Y) (u:X->Y) (v:Y->X) a
    (hu:@norm_analytic_at R X Y NX NY hNX hNY A u a)
    (hv:@norm_analytic_at R Y X NY NX hNY hNX B v (u a)):
  (forall y,u (v y) = y) ->v (u a) = a ->
  injective (@analytic_germ_ring_pullback R X Y NX NY hNX hNY A u a hu).
Proof.
move=>hInverse hPoint alpha beta hEqual.
pose TX:=Topological.clone (real_norm_metric_space hNX) _.
pose TY:=Topological.clone (real_norm_metric_space hNY) _.
pose PX:=@analytic_representative_type R X NX hNX a.
pose PY:=@analytic_representative_type R Y NY hNY (u a).
pose valueX:=@analytic_representative_value R X NX hNX a.
pose valueY:=@analytic_representative_value R Y NY hNY (u a).
have [f hf]:=@analytic_germ_has_representative R Y NY hNY (u a) alpha.
have [g hg]:=@analytic_germ_has_representative R Y NY hNY (u a) beta.
have hPullback:analytic_germ (@analytic_pullback_representative R X Y NX NY hNX hNY A u a hu f) =
    analytic_germ (@analytic_pullback_representative R X Y NX NY hNX hNY A u a hu g).
  rewrite -!(@AnalyticPullback.laws R X Y NX NY hNX hNY A u a hu) hf hg.
  exact:hEqual.
have [U [hU [haU hAgreement]]]:=(local_germ_equality (@LocalGerms.laws TX R PX valueX a) _ _).1 hPullback.
have [V [haV [_ [_ hV]]]]:=analytic_germ_open_representative hv.
pose W:set Y:=fun y=>V y /\U (v y).
have hW:@open (real_norm_metric_space hNY) W.
  exact:(@norm_class_zero_open_preimage R Y X NY NX hNY hNX V U v
    (norm_class_continuous (norm_analytic_class_all_orders hV 0%N)) hU).
have hCentre:W (u a) by split;last by rewrite hPoint.
rewrite -hf -hg;apply/(local_germ_equality (@LocalGerms.laws TY R PY valueY (u a)) f g).
exists W;split;first exact:hW.
split;first exact:hCentre.
move=>y hy;have hh:=hAgreement (v y) hy.2.
change (analytic_representative_value f (u (v y)) =
  analytic_representative_value g (u (v y))) in hh.
by rewrite hInverse in hh.
Qed.
