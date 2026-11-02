(** Private containing-ball witnesses for Federer (1969), 2.10.19(3)–(5), p.
    181. When diam S=0, retain the original positive-radius ball instead of
    introducing a radius-zero generator. The implementation is exposed only
    through its sealed weak-enlargement laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology ring lra.
From Federer Require Import MetricClosedBalls MetricDiameterUP MetricDiameter EuclideanBallDiameter
  HausdorffMeasureUP HausdorffDiameterCost HausdorffPowerCostLaws DiameterEnlargements
  CaratheodoryWeakEnlargementUP SphericalEnlargementUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_ball_enlargement_exists]: private witness for the
    containing-ball step in 2.10.19, p. 181 The empty family is not used:
    positive-radius balls contain their centre. Diameter zero is handled
    with the same positive-radius ball, preserving 2.8.1. *)
Theorem spherical_ball_enlargement_exists (R : realType) (X : metricType R)
    (m : nat) (a : X) (r : R) : 0<r -> exists U : set X,
  is_positive_metric_closed_ball U /\
  (extended_metric_diameter U<=(spherical_enlargement_control R m)%:E*
    extended_metric_diameter (metric_closed_ball a r))%E /\
  diameter_enlargement (@is_positive_metric_closed_ball R X) (metric_closed_ball a r) `<=` U /\
  (hausdorff_diameter_cost m U<=(spherical_enlargement_control R m)%:E*
    hausdorff_diameter_cost m (metric_closed_ball a r))%E.
Proof.
move=> hr; pose S := metric_closed_ball a r.
pose k := spherical_enlargement_control R m.
have hkp : 0<k := spherical_enlargement_control_positive R m.
have hk10 : 10<=k := spherical_enlargement_control_ge_ten R m.
have hk1 : 1<=k.
  have h1 : (1<=10 :> R) by rewrite ler1n.
  exact: le_trans h1 hk10.
have hkc : (10 : R)^+m<=k := spherical_enlargement_control_ge_power R m.
have haS : S a by rewrite /S /metric_closed_ball /= mdistxx; exact: ltW hr.
have hdn := metric_diameter_nonnegative (extended_metric_diameter_specification S).
have hdb := metric_ball_diameter_upper a (ltW hr).
have hdnum : extended_metric_diameter S \is a fin_num.
  rewrite (ge0_fin_numE hdn); exact: le_lt_trans hdb (@ltry R (r+r)).
pose d := fine (extended_metric_diameter S).
have hD : extended_metric_diameter S=d%:E by rewrite /d fineK.
have hd0 : 0<=d by move: hdn; rewrite hD lee_fin.
have hd2r : d<=r+r by move: hdb; rewrite hD lee_fin.
have hcostS := @hausdorff_diameter_cost_nonnegative R X m S.
case: (eqVneq d 0)=> [hzero|hnz].
- exists S; split; first exact: positive_closed_ball_satisfies_laws hr.
  split.
  + by rewrite hD hzero mule0.
  + split.
    * move=> x [T [hT [hmeet hTd]] hx].
      have [y [hyT hyS]] : exists y, (T `&` S) y.
        apply: (set0P _).1; by apply/eqP.
      have hb := le_trans (metric_diameter_upper (extended_metric_diameter_specification T) hyT hx) hTd.
      rewrite hD hzero mule0 lee_fin in hb.
      have hyx : y=x.
        apply: mdist_positivity; apply/eqP; by rewrite eq_le mdist_ge0 andbT.
      by rewrite -hyx.
    * have hkE : (1<=k%:E)%E by rewrite lee_fin.
      have hh := lee_wpmul2r hcostS hkE; by rewrite mul1e in hh.
- have hdp : 0<d by rewrite lt_def hnz hd0.
  pose s := Num.min r d.
  have hs : 0<s by rewrite /s lt_min hr hdp.
  have hsr : s<=r by rewrite /s ge_min lexx.
  have hsd : s<=d by rewrite /s ge_min lexx orbT.
  have hd2s : d<=2*s.
    case: (leP r d)=> h.
    - rewrite /s (min_idPl h); lra.
    - rewrite /s (min_idPr (ltW h)); lra.
  pose U := metric_closed_ball a (5*s).
  have hrad : 0<5*s by rewrite mulr_gt0 // ltr0n.
  have hUdiam : (extended_metric_diameter U<=(10*s)%:E)%E.
    have hh := metric_ball_diameter_upper a (ltW hrad).
    have he : 5*s+5*s = 10*s by ring.
    by rewrite he in hh.
  have hU10 : (extended_metric_diameter U<=(10*d)%:E)%E.
    apply: le_trans hUdiam _; rewrite lee_fin.
    apply: ler_wpM2l hsd; by rewrite ler0n.
  exists U; split; first exact: positive_closed_ball_satisfies_laws hrad.
  split.
  + apply: le_trans hU10 _; rewrite hD -EFinM lee_fin.
    by rewrite (ler_pM2r hdp).
  + split.
    * move=> x [T [hT [hmeet hTd]] hx].
      have [y [hyT hyS]] : exists y, (T `&` S) y.
        apply: (set0P _).1; by apply/eqP.
      have hayr : mdist a y<=r := hyS.
      have hayd := metric_diameter_upper (extended_metric_diameter_specification S) haS hyS.
      rewrite hD lee_fin in hayd.
      have hays : mdist a y<=s by rewrite /s le_min; apply/andP.
      have hyx := le_trans (metric_diameter_upper (extended_metric_diameter_specification T) hyT hx) hTd.
      rewrite hD -EFinM lee_fin in hyx.
      have htri := metric_triangle a y x.
      change (is_true (mdist a x<=5*s)); lra.
    * have hcost10 : (hausdorff_diameter_cost m U<=((10 : R)^+m)%:E*hausdorff_diameter_cost m S)%E.
        have hh := @hausdorff_power_cost_monotone R m (extended_metric_diameter U) (10*d)%:E
          (metric_diameter_nonnegative (extended_metric_diameter_specification U)) hU10.
        have he : hausdorff_normalisation R m*(10*d)^+m=
            (10 : R)^+m*(hausdorff_normalisation R m*d^+m).
          rewrite exprMn; ring.
        move: hh; rewrite hausdorff_power_cost_finite he EFinM.
        by rewrite /hausdorff_diameter_cost hD hausdorff_power_cost_finite.
      have hkcE : (((10 : R)^+m)%:E<=k%:E)%E by rewrite lee_fin.
      have hh := lee_wpmul2r hcostS hkcE.
      exact: le_trans hcost10 hh.
Qed.

(** Source for [spherical_enlargement_exists]: private choice of the
    containing ball for each generator in 2.10.19, p. 181 Only the proved
    weak enlargement laws are exposed by the sealing module. *)
Theorem spherical_enlargement_exists (R : realType) (X : metricType R) (m : nat) :
  exists E : set X -> set X, is_weak_caratheodory_enlargement
    (@is_positive_metric_closed_ball R X) (@hausdorff_diameter_cost R X m) E (spherical_enlargement_control R m).
Proof.
have hex S : exists U, is_positive_metric_closed_ball S ->
    is_positive_metric_closed_ball U /\
    (extended_metric_diameter U<=(spherical_enlargement_control R m)%:E*extended_metric_diameter S)%E /\
    diameter_enlargement (@is_positive_metric_closed_ball R X) S `<=` U /\
    (hausdorff_diameter_cost m U<=(spherical_enlargement_control R m)%:E*hausdorff_diameter_cost m S)%E.
  case: (pselect (is_positive_metric_closed_ball S))=> hS.
  - have [a [r [hr hrepr]]] := hS.
    have he : S=metric_closed_ball a r.
      apply/seteqP; split=> x hx.
      + exact: (hrepr x).1 hx.
      + exact: (hrepr x).2 hx.
    rewrite he; have [U hU] := @spherical_ball_enlargement_exists R X m a r hr.
    by exists U.
  - exists S=> h; exfalso; exact: hS h.
pose E S := projT1 (cid (hex S)).
have hE S := projT2 (cid (hex S)).
exists E; constructor.
- exact: spherical_enlargement_control_positive.
- move=> S _; exact: hausdorff_diameter_cost_nonnegative.
- move=> S hS; exact: (hE S hS).1.
- move=> S hS; exact: (hE S hS).2.2.1.
- move=> S hS; exact: (hE S hS).2.1.
- move=> S hS; exact: (hE S hS).2.2.2.
Qed.
