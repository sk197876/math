(** Federer (1969), 3.2.41, printed p. 278, final proof paragraph:
    translate a set before or after taking its actual density-one
    hull. This supporting pointwise identity uses the exact outer
    Lebesgue translation law, including for nonmeasurable sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanLebesgueTranslation EuclideanAdditiveGroup
  EuclideanNoncenteredVitali EuclideanClosedBallVolume CenteredBallRelations MeasureDensityPoints MeasureSetDensity
  CenteredFiniteDensityIsometry MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section Translation.
Variable R:realType.
Variable n:nat.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Leb:=(@euclidean_lebesgue_measure R n).
Local Notation V:=(@centered_closed_ball_relation R [the metricType R of E]).

(** Source for [euclidean_finite_density_translation_preimage]:
    supporting translation of the finite density in the hull
    argument of Federer 3.2.41, p. 278. The assertion retains
    the actual set and the value of its full centered density. *)
Lemma euclidean_finite_density_translation_preimage (A:set E) (a x:E) (c:R):
  partial_function_graph (measure_set_density Leb V A) (a+x)%R c%:E ->
  partial_function_graph (measure_set_density Leb V
    ((fun z:E=>(a+z)%R) @^-1` A)) x c%:E.
Proof.
apply:(@centered_finite_density_isometric_preimage R [the metricType R of E]
  [the metricType R of E] Leb Leb (fun z:E=>(a+z)%R) (fun z:E=>(-a+z)%R) A x c).
- by move=> z; rewrite addKr.
- by move=> z; rewrite addNKr.
- by move=> u v; rewrite !inner_metric_distanceE opprD addrACA subrr add0r.
- move=> B; symmetry.
  exact:(congr1 (fun mu:set E->\bar R=>mu B)
    (@euclidean_lebesgue_translation_pushforward R n a)).
- move=> z r hr; split; first exact:euclidean_closed_ball_positive hr.
  by rewrite (euclidean_closed_ball_normalized_volume z (ltW hr)) fin_numE.
- move=> z r hr; split; first exact:euclidean_closed_ball_positive hr.
  by rewrite (euclidean_closed_ball_normalized_volume z (ltW hr)) fin_numE.
Qed.

(** Source for [euclidean_density_one_translation_preimage]: exact
    pointwise hull translation for Federer 3.2.41, p. 278.
    Undoing the actual inverse translation proves the converse;
    no almost-everywhere replacement is used. *)
Lemma euclidean_density_one_translation_preimage (A:set E) (a x:E):
  measure_density_one_points Leb V ((fun z:E=>(a+z)%R) @^-1` A) x <->
    measure_density_one_points Leb V A (a+x)%R.
Proof.
split; last exact:euclidean_finite_density_translation_preimage.
move=> hx.
pose B:=(fun z:E=>(a+z)%R) @^-1` A.
have hx':partial_function_graph (measure_set_density Leb V B) (-a+(a+x))%R 1.
  by rewrite addKr.
have h:=@euclidean_finite_density_translation_preimage B (-a)%R (a+x)%R 1 hx'.
have he:(fun z:E=>(-a+z)%R) @^-1` B=A.
  apply/seteqP; split=> z; change (A (a+(-a+z))%R->A z) ||
    change (A z->A (a+(-a+z))%R); by rewrite addNKr.
by rewrite he in h.
Qed.

(** Source for [euclidean_density_one_hull_translation]: supporting
    exact set identity for S* in Federer 3.2.41, p. 278.
    Translation preserves the whole actual density-one point set. *)
Lemma euclidean_density_one_hull_translation (A:set E) (a:E):
  measure_density_one_points Leb V [set (a+x)%R |x in A]=
    [set (a+x)%R |x in measure_density_one_points Leb V A].
Proof.
pose T:=[set (a+x)%R |x in A].
have hPre:(fun z:E=>(a+z)%R) @^-1` T=A.
  apply/seteqP; split=> z.
  - move=> [x hx he].
    have hEq:x=z.
      have h:=congr1 (fun w:E=>(-a+w)%R) he; by rewrite !addKr in h.
    by rewrite -hEq.
  - move=> hz; by exists z.
apply/seteqP; split=> z.
- move=> hz; exists (-a+z)%R; last by rewrite addNKr.
  have hPoint:measure_density_one_points Leb V T (a+(-a+z))%R by rewrite addNKr.
  have h:=(@euclidean_density_one_translation_preimage T a (-a+z)%R).2 hPoint.
  by rewrite hPre in h.
- move=> [x hx <-].
  apply:(@euclidean_density_one_translation_preimage T a x).1.
  by rewrite hPre.
Qed.
End Translation.
