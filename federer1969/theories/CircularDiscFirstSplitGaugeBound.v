(** Federer (1969), 3.3.19, pp. 303–304:
    assemble the original first-split alternative from
    actual boundary points, scalar margins, centre
    separation and the original hit-measure decomposition. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex MetricClosedBalls CoveringFamilyUP
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularTrigonometrySealed CircularDiscTreeUP CircularDiscRefinement CircularDiscFirstSplitUP CircularDiscFirstSplit
  CircularDiscBoundarySelection CircularDiscCentreDistances RadialBallRetractionUP
  CircularDiscHitCount CircularDiscHitMeasureUP CircularDiscHitSelectedDecomposition FiniteCellHitMeasureUP FiniteCellHitIndicesLaws
  RetractionPairWeightBudget CircularDiscLocalBoundaryBudget ConvexBoundaryFiniteWeightBudget ConvexBodyCauchy IntegralGeometricGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Split.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation Sin:=(@CircularTrigonometry.sine R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable psi:nat->set E->\bar R.
Hypothesis hPsi:is_circular_disc_hit_measures H psi.

(** Source for [circular_disc_first_split_gauge_bound]:
    q(S)>=lambda psi_(n+1)(S) for the original
    first-split alternative in 3.3.19,
    pp. 303–304. The curve, its ordering,
    the radial map and all boundary points are
    constructed locally; none is an extra premise. *)
Theorem circular_disc_first_split_gauge_bound j (lam:R) (S:set E):
  0<lam ->lam<((j+4)%:R-1)* Sin (p/(j+4)%:R) ->
  lam*(1/2+((j+4).+1)%:R^-1)<((j+4)%:R-1)* Sin (p/(j+4)%:R)-1 ->
  open S ->is_inner_convex S ->metric_set_bounded S ->
  is_circular_first_split H S j.+1 ->
  (lam%:E* psi j.+2 S<=@integral_geometric_gauge R 2 1 (leqnSn 1) 1 S)%E.
Proof.
move=>hLam hFirst hSecond hOpen hConvex hBound hSplit.
have [z [hz [hParentHits hParent]]]:= @circular_disc_first_split_parent R H S hH j hSplit.
pose F:= @circular_disc_hit_indices R H j.+1 S.
pose I:finType:=[the finType of (F:Type)].
pose c:I->E:= fun i=>val i.
have hHits i:c i \in F:= valP i.
have hOriginal i:c i \in H j.+1 /\exists x,metric_closed_ball (c i) (rho j.+1) x /\S x.
  exact:(@finite_cell_hit_indices_membership E E (H j.+1)
    (fun u=>metric_closed_ball u (rho j.+1)) S (c i)).1 (hHits i).
have hChild i:exists k:'I_(j+4),c i= circular_disc_child_center z (rho j) k:= hParent (c i) (hHits i).
have [index hIndex]:= choice hChild.
have hRadius:0<rho j:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho
  (@FactorialDiscScales.laws R) j.
have hn:(4<=j+4)%N:= leq_addl j 4.
have [P [hP hSelection]]:= @circular_disc_boundary_selection_exists R z (rho j) (j+4)%N S
  hRadius hn hOpen hConvex hBound.
have hPoints i:exists xi:E,(closure S `\` interior S) xi /\
    metric_closed_ball (c i) (rho j.+1) (P xi) /\(S (c i) ->P xi= c i).
  have hMeeting:metric_closed_ball (circular_disc_child_center z (rho j) (index i))
      (rho j/(j+4)%:R) `&` S!=set0.
    have [x [hxB hxS]]:=(hOriginal i).2;exists x;split=>//.
    by rewrite -hIndex -(factorial_disc_radius_step (@FactorialDiscScales.laws R)).
  have [xi [hBoundary [hBall hCentre]]]:= hSelection (index i) hMeeting.
  exists xi;split=>//;split.
  - by rewrite hIndex (factorial_disc_radius_step (@FactorialDiscScales.laws R)).
  - by rewrite hIndex.
have [xi hXi]:= choice hPoints.
pose b:R:=((j+4)%:R-1)* Sin (p/(j+4)%:R)* rho j.+1.
pose v i:R:=#|` @circular_disc_hit_indices R H j.+2 (metric_closed_ball (c i) (rho j.+1) `&` S)|%:R* rho j.+2.
pose w i:R:= lam* v i.
have hNonempty:S!=set0.
  have /card_gt0P[i]: (0<#|I|)%N.
    rewrite cardT -cardE -cardfE /F;exact:(leq_trans (erefl true : (1<=2)%N) hSplit.1).
  have [x [_ hxS]]:=(hOriginal i).2;by exists x.
have hLocal i:w i<=b-mdist (P (xi i)) (c i).
  have hBudget:= @circular_disc_local_boundary_budget R H hH psi hPsi j lam (c i) S (P (xi i))
    hLam hFirst hSecond (hOriginal i).1 hNonempty hConvex (hXi i).2.1 (hXi i).2.2.
  rewrite (hPsi j.+2) -EFinM lee_fin in hBudget;exact hBudget.
have hSeparation i k:i!=k ->2* b<=mdist (c i) (c k).
  move=>hDifferent.
  have hDistinct:c i!=c k.
    apply/negP=>/eqP hEqual;have hSame:i= k:= val_inj hEqual.
    by move:hDifferent;rewrite hSame eqxx.
  have hIndexDifferent:index i!=index k.
    apply/negP=>/eqP hEqual;move:hDistinct;by rewrite !hIndex hEqual eqxx.
  have hCentres:= @circular_disc_centre_minimum R z (rho j) (j+4)%N (index i) (index k)
    hRadius hn hIndexDifferent.
  rewrite -!hIndex in hCentres.
  have hNN:((j+4)%:R:R)!=0 by rewrite pnatr_eq0 addn_eq0 andbF.
  have hScale:(1-(j+4)%:R^-1)* rho j=((j+4)%:R-1)* rho j.+1.
    rewrite (factorial_disc_radius_step (@FactorialDiscScales.laws R));field;by rewrite -natrD.
  rewrite hScale in hCentres.
  have hSame:2*(((j+4)%:R-1)* rho j.+1)* Sin (p/(j+4)%:R)= 2* b by rewrite /b;ring.
  by rewrite hSame in hCentres.
have hPair i k:i!=k ->w i+w k<=mdist (xi i) (xi k).
  move=>hDifferent.
  have hRetract:=(@radial_ball_retraction_nonexpanding R (R_n R 2) (@euclidean_inner_product R 2)
    (@euclidean_inner_productP R 2) z (rho j-rho j/(j+4)%:R) P hP).2 (xi i) (xi k) Logic.I Logic.I.
  rewrite mul1r in hRetract.
  exact:(@retraction_pair_weight_budget R [the metricType R of E] P (c i) (c k) (xi i) (xi k) b
    (w i) (w k) (hSeparation i k hDifferent) (hLocal i) (hLocal k) hRetract).
have hCard:(2<=#|I|)%N.
  rewrite cardT -cardE -cardfE /F;exact hSplit.1.
have hBudget:= @convex_boundary_finite_weight_budget R I S xi w hNonempty hOpen hConvex hBound hCard
  (fun i=>(hXi i).1) hPair.
have hDecomposition:= @circular_disc_hit_selected_decomposition R H psi hH hPsi j.+1 j.+2 S (leqnSn j.+1).
have hMass:psi j.+2 S=(\sum_(i:I) v i)%:E.
  rewrite hDecomposition big_seq_fsetE -sumEFin.
  apply:eq_bigr=>i _;exact:(hPsi j.+2 _).
have hWeighted:(lam%:E*psi j.+2 S=(\sum_(i:I) w i)%:E)%E.
  rewrite hMass -EFinM;congr (_%:E);by rewrite mulr_sumr.
rewrite (@convex_body_cauchy_formula R 1 S hNonempty hOpen hConvex hBound) EFinM in hBudget.
rewrite hWeighted.
have hPositive:(0<(2:R)%:E)%E by rewrite lte_fin;exact:(ltr0n R 2).
have hFinite:(2:R)%:E \is a fin_num by rewrite fin_numE.
move:hBudget;rewrite (lee_pmul2l hFinite hPositive).
by [].
Qed.
End Split.
