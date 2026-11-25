(** Federer (1969), 2.9.16, p. 161: the counterexample using all closed
    balls containing the base point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP BorelRegularMeasureUP MeasureDerivationContext
  MetricClosedBalls MetricDiameterUP MetricDiameter CoveringFamilyUP CoveringFamilyLaws
  CoveringRelationUP CoveringRelationFineness CoveringRelationLimits PartialFunctionUP
  NoncenteredBallRelations DiametricRegularityUP DiameterWeightLaws BallEnlargementBound
  WeightedEnlargements FamilyWeightedEnlargements EnlargementRatio EnlargementVitaliCriterion
  ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.


(** Source for [doubling_noncentered_balls_vitali]: supporting
    ball criterion for Federer 2.9.16, p. 161,
    expanding its references to 2.8.17 and 2.8.8. A finite uniform fivefold growth
    bound and positive ball masses suffice in any metric space.
    The proof uses diameter as weight and tau=2; the corrected
    positivity hypothesis of 2.8.17 is explicit (erratum p. 3,
    book p. 151 line 24). This supporting version has a
    global growth bound; the Euclidean example proves that bound. *)
Theorem doubling_noncentered_balls_vitali (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (c : R) :
  is_derivation_measure phi -> (0<=c)%R ->
  (forall a r, (0<r)%R -> 0<phi (metric_closed_ball a r)) ->
  (forall a r, (0<r)%R -> phi (metric_closed_ball a (5*r)%R)<=c%:E*phi (metric_closed_ball a r)) ->
  is_vitali_relation phi (@noncentered_closed_ball_relation R X).
Proof.
move=> hphi hc hpos hg; have hm := derivation_measure_law hphi.
pose V := @noncentered_closed_ball_relation R X.
pose F := covering_relation_image V setT.
have hballs S : F S -> exists a r, (0<r)%R /\ S=metric_closed_ball a r.
  exact: (@noncentered_closed_ball_image R X S).1.
have hb S : F S -> metric_set_bounded S.
  move=> /hballs [a [r [hr ->]]]; exact: covering_closed_ball_bounded (ltW hr).
have hF : is_covering_theory_context F phi.
  constructor=> //.
  - move=> S /hballs [a [r [_ ->]]]; exact: metric_closed_ball_closed.
  - exact: borel_regular_open_measurable (derivation_measure_borel_regular hphi).
  - exact: derivation_measure_bounded_finite hphi.
have hp S : F S -> 0<phi S.
  by move=> /hballs [a [r [hr ->]]]; exact: hpos.
have [w hw] := @real_diameter_weight_exists R X F hb.
pose delta (S : {S : set X | F S}) := w (sval S).
have hn S : (0<=delta S)%R := @diameter_weight_nonnegative R X F w hw (sval S) (proj2_sig S).
have hext : is_family_weight_extension delta w by move=> S hS.
pose f := family_enlargement_ratio_function phi delta 2%R.
have hvalue (S : {S : set X | F S}) :
    0<=family_enlargement_ratio_value phi delta 2%R S /\
    family_enlargement_ratio_value phi delta 2%R S<=(w (sval S))%:E+c%:E.
  pose A := sval S; have hA : F A := proj2_sig S.
  have [a [r [hr hAr]]] := hballs A hA.
  have hfin : phi A \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative hm A)); exact (@derivation_measure_bounded_finite R X phi hphi A (hb A hA)).
  have hq : (0<fine (phi A))%R by rewrite -lte_fin fineK //; exact: hp A hA.
  have hi : (0<=((fine (phi A))^-1))%R by rewrite invr_ge0; exact: ltW hq.
  have hhat : phi (weighted_enlargement F w 2%R A)<=c%:E*phi A.
    have hBa : F (metric_closed_ball a r) by rewrite -hAr.
    have hinc := @diameter_enlargement_ball_bound R X F w 2%R hw
      (ltac:(by rewrite ler0n)) a r hBa (ltW hr).
    have h5 : ((1+2*2)*r=5*r)%R by lra.
    rewrite h5 in hinc; rewrite hAr.
    exact: le_trans (@measure_mono R X phi hm _ _ hinc) (hg a r hr).
  rewrite (@family_enlargement_ratio_extension R X phi F delta w 2%R hext S).
  have hw0 : 0<=(w A)%:E by rewrite lee_fin; exact: hn.
  have hm0 : 0<=phi (weighted_enlargement F w 2%R A)*((fine (phi A))^-1)%:E.
    apply: mule_ge0; first exact (@measure_nonnegative R X phi hm _).
    by rewrite lee_fin.
  split; first exact: adde_ge0 hw0 hm0.
  apply: leeD (lexx _) _.
  have hbmul := @lee_wpmul2r R ((fine (phi A))^-1)%:E (ltac:(by rewrite lee_fin))
    _ _ hhat.
  have hq0 : fine (phi A)!=0%R by rewrite (gt_eqF hq).
  have hcancel : (c%:E*phi A)*((fine (phi A))^-1)%:E=c%:E.
    by rewrite -(fineK hfin) -!EFinM mulfK.
  by rewrite hcancel in hbmul.
have hu x : 0<=covering_upper_limit V f x< +oo.
  apply/andP; split.
  - apply: extended_real_inf_greatest=> b [e [he ->]].
    have [A [hVA hdiam]] := (covering_relation_fine_iff_small_diameter V x).1
      (@noncentered_closed_balls_fine R X x) e he.
    have hA : F A by exists x.
    pose S := exist F A hA.
    have hrange : covering_value_range V f x e
        (family_enlargement_ratio_value phi delta 2%R S).
      exists A; split=> //; split=> //.
      exact (@family_enlargement_ratio_graph R X phi F delta 2%R S).
    exact: le_trans (hvalue S).1 (extended_real_sup_upper hrange).
  - apply: le_lt_trans (@covering_upper_limit_le_level R X V f x 1%R (ltr01)) _.
    apply: le_lt_trans _ (@ltry R (1+c)%R).
    apply: extended_real_sup_least=> y [A [hVA [hdiam [S [hSA hval]]]]].
    rewrite -hval; apply: le_trans (hvalue S).2 _.
    have he : extended_metric_diameter (sval S)=(w (sval S))%:E.
      exact: metric_diameter_unique (extended_metric_diameter_specification _) (hw _ (proj2_sig S)).
    have hw1 : (w (sval S))%:E<= 1.
      apply: ltW; by rewrite -he hSA.
    by rewrite EFinD; exact: leeD hw1 (lexx _).
apply: (@federer_2_8_17 R X phi V delta 2%R hF
  (@noncentered_closed_balls_covering R X) (@noncentered_closed_balls_fine R X)
  hb hp hn (ltac:(by rewrite ltr1n))).
have he : [set x | 0<=covering_upper_limit V f x< +oo]=setT.
  apply/seteqP; split=> x // _; exact: hu.
by rewrite /measure_almost_everywhere he setCT; exact: measure_empty hm.
Qed.
