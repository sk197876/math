(** Federer (1969), 3.2.38, pp. 274--275: uniform scalar
    oscillation on the compact Lusin core used to sum good cubes. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialContinuityUP CompactUniformContinuity
  MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_partial_total_uniform_continuity]: supporting
    the Lusin-core variant of the mean comparison in Federer 3.2.38,
    pp. 274--275. Relative continuity, as specified in 2.3.5,
    and compactness give a uniform modulus on the actual core.
    The total representative's values outside it play no role. *)
Lemma compact_partial_total_uniform_continuity (R:realType) (X Y:metricType R)
    (E:set X) (J:X->Y):
  compact E ->partial_function_continuous_on E (partial_function_total J) ->
  forall e:R,0<e ->exists d:R,0<d /\forall a b,
    E a ->E b ->mdist a b<d ->mdist (J a) (J b)<e.
Proof.
move=>hCompact hJ.
apply:compact_uniform_continuity hCompact _.
move=>a ha e he.
have hOpen:open [set z:Y|mdist (J a) z<e]:=metric_open_ball_open (J a) e.
have [V [hV hPreimage]]:=partial_continuity_open hJ hOpen.
have haV:V a.
  have hMember:(E `&` partial_function_preimage (partial_function_total J)
      [set z:Y|mdist (J a) z<e]) a.
    split; first exact ha.
    exists (J a); split; first reflexivity.
    change (is_true (mdist (J a) (J a)<e)); by rewrite mdistxx.
  by rewrite hPreimage in hMember; exact:hMember.2.
have hNeighborhood:nbhs a V by rewrite openE in hV; exact:hV a haV.
have [d hd hBall]:=(metricType_numDomainType.nbhs_mdistP a V).1 hNeighborhood.
exists d; split=>// b hb hab.
have hbV:=hBall b hab.
have hMember:(E `&` partial_function_preimage (partial_function_total J)
    [set z:Y|mdist (J a) z<e]) b by rewrite hPreimage.
have [_ [y [hy hDistance]]]:=hMember.
by rewrite (hy:J b=y).
Qed.
