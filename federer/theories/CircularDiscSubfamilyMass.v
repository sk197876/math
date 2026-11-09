(** Federer (1969), 3.3.19, pp. 304–305: exact mass of
    any finite original level subfamily. This supplies all
    angular-visit and cap budgets using actual pieces of A. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  FactorialDiscScalesSealed CircularDiscTreeUP CircularDiscTreeTopology CircularDiscLimitUP CircularDiscLevelPieces
  CircularDiscPieceHausdorffMass HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic MeasureFiniteAdditivity BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Mass.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_level_subfamily_mass]: for
    any actual subfamily F of G_n, the original
    H1(A intersect union F)= 2 rho_n card(F), as used
    in both measure estimates of 3.3.19, p. 305.
    All actual finite closed pieces are measurable and
    disjoint; neither fact is added as a premise. *)
Theorem circular_disc_level_subfamily_mass j (F:{fset E}):
  (F `<=` H j)%fset ->
  mu (A `&` (\bigcup_(z in [set` F]) metric_closed_ball z (rho j)))=
    (2* rho j*#|` F|%:R)%:E.
Proof.
move=>hF.
have hMu:= @hausdorff_measure_is_measure R [the metricType R of E] 1.
have hReg:= @hausdorff_measure_borel_regular R [the metricType R of E] 1.
have [hNonempty hCompact]:= @circular_disc_limit_nonempty_compact R H hH A hA.
have hAClosed:closed A:= compact_closed (@metric_hausdorff R [the metricType R of E]) hCompact.
pose P:= fun z:E=>A `&` metric_closed_ball z (rho j).
have hMeas z:z \in F ->measure_measurable mu (P z).
  move=>hz;apply:(@borel_regular_borel_measurable R [the topologicalType of E] mu hMu hReg).
  apply:closed_borel_set;apply:closedI;first exact hAClosed.
  exact:metric_closed_ball_closed.
have hDisjoint z w:z \in F ->w \in F ->z!=w ->forall x,P z x ->P w x ->False.
  move=>hz hw hDifferent x [_ hxZ] [_ hxW].
  have hzH:= fsubsetP hF z hz.
  have hwH:= fsubsetP hF w hw.
  have hEqual:= @circular_disc_level_point_unique R H hH j x z w hzH hwH hxZ hxW.
  by move:hDifferent;rewrite hEqual eqxx.
have hPartition:= @measure_finite_disjoint_additivity R E E mu hMu P F hMeas hDisjoint.
have hUnion:(\bigcup_(z in [set` F]) P z)=
    A `&` (\bigcup_(z in [set` F]) metric_closed_ball z (rho j)).
  apply/seteqP;split.
  - move=>x [z hz [hxA hxZ]];split=>//;by exists z.
  - move=>x [hxA [z hz hxZ]];exists z=>//;by split.
rewrite hUnion in hPartition.
rewrite hPartition.
transitivity (\sum_(z<-F) (2* rho j)%:E).
- apply:eq_big_seq=>z hz;exact:(@circular_disc_piece_Hausdorff_mass R H hH A hA j z (fsubsetP hF z hz)).
- by rewrite sumEFin big_seq_fsetE sumr_const cardT -cardE -cardfE mulr_natr.
Qed.
End Mass.
