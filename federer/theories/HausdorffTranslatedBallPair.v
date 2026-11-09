(** Federer (1969), 3.3.19, p. 306: disjoint
    pulled-back ball tests on congruent original pieces
    control their combined mass in the last density proof. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerTranslationNeighbourhood
  MetricClosedBalls HausdorffMeasure HausdorffClosedCoverAgreement HausdorffIsometricEmbedding
  MeasureUP MeasureBasic MeasureFiniteAdditivity BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Pair.
Variable R:realType.
Variable V:lmodType R.
Variable B:V->V->R.
Hypothesis hB:is_inner_product B.
Local Notation E:=(inner_metric_space hB).
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).

(** Source for [hausdorff_translated_ball_pair_bound]: if
    two original translates differ by a vector longer than
    the test ball's diameter, their pulled-back tests are
    disjoint subsets of one original piece. Their combined
    H1 mass is at most that piece's full mass. This
    supports the three-child case of the final upper-density
    assertion in 3.3.19, p. 306. *)
Theorem hausdorff_translated_ball_pair_bound (P:set E) (a h:E) (t:R):
  closed P ->2* t<inner_norm hB h ->
  (mu (P `&` metric_closed_ball a t)+
    mu (((fun x:E=>(x+h)%R) @` P) `&` metric_closed_ball a t)<=mu P)%E.
Proof.
move=>hP hFar.
pose C:= P `&` metric_closed_ball a t.
pose D:= P `&` ((fun x:E=>(x+h)%R) @^-1` metric_closed_ball a t).
have hImage:((fun x:E=>(x+h)%R) @` D)=
    ((fun x:E=>(x+h)%R) @` P) `&` metric_closed_ball a t.
  apply/seteqP;split.
  - move=>y [x [hxP hxBall] <-];split=>//;by exists x.
  - move=>y [[x hxP <-] hxBall];exists x=>//;by split.
have hInverse:cancel (fun x:E=>(x+h)%R) (fun x:E=>x-h) by move=>x;rewrite addrK.
have hMass:= @hausdorff_isometric_embedding_invariance R [the metricType R of E] [the metricType R of E]
  (fun x:E=>(x+h)%R) (fun x:E=>x-h) hInverse
  (fun x y=>@inner_translation_distance R V B hB h x y) 1 D.
rewrite hImage in hMass.
have hDisjoint:forall x,C x ->D x ->False.
  move=>x [_ hx] [_ hxh].
  have hTriangle:= metric_triangle x a (x+h).
  rewrite (metric_sym x a) in hTriangle.
  have hDistance:mdist x (x+h)= inner_norm hB h.
    by rewrite inner_metric_distanceE opprD addrA subrr add0r inner_normN.
  rewrite hDistance in hTriangle.
  have hxR:mdist a x<=t:= hx.
  have hxhR:mdist a (x+h)<=t:= hxh.
  lra.
have hMu:= @hausdorff_measure_is_measure R E 1.
have hMeas:measure_measurable mu C.
  apply:(@borel_regular_borel_measurable R E mu hMu (@hausdorff_measure_borel_regular R E 1)).
  apply:closed_borel_set;apply:closedI=>//;exact:metric_closed_ball_closed.
have hUpper:= @measure_mono R E mu hMu (C `|` D) P (fun x hx=>
  match hx with or_introl h=>h.1 |or_intror h=>h.1 end).
rewrite (measure_disjoint_union hMeas hDisjoint) in hUpper.
by rewrite hMass.
Qed.
End Pair.
