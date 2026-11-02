(** Federer (1969), 3.2.31, p. 269: supporting null boundaries
    of the compact refinement. The closed and open ball formulas
    from 2.7.16, p. 135, and 2.10.27, pp. 190–191, give equal
    finite Lebesgue masses at every positive radius. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  InnerNormedTopology MetricClosedBalls TopologicalBorel MeasureUP MeasureBasic
  BorelRegularMeasureUP EuclideanLebesgueDimensions EuclideanBallVolume EuclideanClosedBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section BallShell.
Variable R:realType.
Variable m:nat.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R m)).

(** Source for [euclidean_positive_ball_shell_null]: supporting
    compact-piece refinement for Federer 3.2.31, p. 269.
    Every positive-radius closed ball differs from its open ball
    by a Lebesgue null set. All natural dimensions are included;
    in dimension zero that difference is empty. *)
Theorem euclidean_positive_ball_shell_null (a:E) (r:R):
  (0<r)%R ->
  @euclidean_lebesgue_measure R m
    (metric_closed_ball a r `\` [set x| (mdist a x<r)%R])=0.
Proof.
move=>hr.
pose Leb:=@euclidean_lebesgue_measure R m.
pose Bo:set E:=[set x|(mdist a x<r)%R].
pose Bc:set E:=metric_closed_ball a r.
have hm:=euclidean_lebesgue_is_measure R m.
have hBo:measure_measurable Leb Bo.
  apply:(borel_regular_borel_measurable hm (euclidean_lebesgue_borel_regular R m)).
  apply:open_borel_set; exact:metric_open_ball_open.
have hSub:Bo `<=` Bc by move=>x hx; exact:ltW hx.
have hInter:Bc `&` Bo=Bo by apply/setIidPr.
pose v : \bar R :=(euclidean_unit_ball_volume R m*r^+m)%R%:E.
have hv:v \is a fin_num by [].
have hOpen:Leb Bo=v.
  have hSet:Bo=[set x:E|(`|x-a|<r)%R].
    apply/seteqP; split=>x hx.
    - have hx':(mdist a x<r)%R:=hx.
      rewrite inner_metric_normE in hx'; exact hx'.
    - have hx':(`|x-a|<r)%R:=hx.
      change (is_true (mdist a x<r)%R); by rewrite inner_metric_normE.
  by rewrite hSet; exact:(euclidean_ball_measure a hr).
have hClosed:Leb Bc=v:=euclidean_closed_ball_normalized_volume a (ltW hr).
have h:=hBo Bc.
rewrite hInter hOpen hClosed in h.
change (Leb (Bc `\` Bo)=0).
rewrite -[Leb (Bc `\` Bo)](addeK _ hv) (addeC _ v) -h.
exact:subee hv.
Qed.

End BallShell.
