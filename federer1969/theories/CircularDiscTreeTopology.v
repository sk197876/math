(** Federer (1969), 3.3.19, p. 302: actual child
    containment, nested finite compact level unions and
    compactness of the original intersection. All statements
    follow from the public recurrences, without a separation
    or measure premise. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  EuclideanClosedBallCompact CompactNestedIntersection FactorialDiscScalesUP
  FactorialDiscScalesSealed FactorialDiscScaleLaws CircularUnitVectors
  CircularDiscRefinement CircularDiscTreeUP CircularDiscLimitUP InnerCircularChildBall.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Topology.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation hs:=(@FactorialDiscScales.laws R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_child_containment]: every
    actual disc in the original F_n(D) lies in D,
    supporting the nested intersection in 3.3.19, p. 302. *)
Lemma circular_disc_child_containment j (z:E) (k:'I_(j+4)):
  metric_closed_ball (circular_disc_child_center z (rho j) k) (rho j.+1)
    `<=` metric_closed_ball z (rho j).
Proof.
rewrite (factorial_disc_radius_step hs) /circular_disc_child_center.
apply:inner_circular_child_ball_subset;first exact:circular_unit_vector_norm.
- exact:ltW (factorial_disc_radius_positive hs j).
- by rewrite ler1n addn_gt0 orbT.
Qed.

(** Source for [circular_disc_level_compact]: finite
    original level unions are compact, as used on
    pp. 302–303 in 3.3.19. *)
Lemma circular_disc_level_compact j:compact (circular_disc_level_union H j).
Proof.
have hFinite (F:{fset E}):compact [set x:E|exists z,z \in F /\metric_closed_ball z (rho j) x].
  elim/fset1U_rect:F=>[|z F hz ih].
  - have hEq:[set x:E|exists z,z \in fset0 /\metric_closed_ball z (rho j) x]= set0.
      apply/seteqP;split=>[x [a [ha _]]|x []];by move:ha;rewrite in_fset0.
    by rewrite hEq;exact:compact0.
  - have hEq:[set x:E|exists a,a \in (z|`F)%fset /\metric_closed_ball a (rho j) x]=
      metric_closed_ball z (rho j) `|` [set x:E|exists a,a \in F /\metric_closed_ball a (rho j) x].
      apply/seteqP;split.
      + move=>x [a [ha hx]];move:ha;rewrite !inE=>/orP[/eqP hEq|ha].
        * subst a;by left.
        * right;by exists a.
      + move=>x [hx|[a [ha hx]]].
        * exists z;split=>//;by rewrite !inE eqxx.
        * exists a;split=>//;by rewrite !inE ha orbT.
    rewrite hEq;apply:compactU.
    + exact:(@euclidean_closed_metric_ball_compact R 2 z (rho j)).
    + exact:ih.
exact:hFinite.
Qed.

(** Source for [circular_disc_level_closed]: original
    level unions are closed, supporting 3.3.19, p. 302. *)
Lemma circular_disc_level_closed j:closed (circular_disc_level_union H j).
Proof. exact (@compact_closed [the topologicalType of E] (circular_disc_level_union H j)
  (@metric_hausdorff R E) (@circular_disc_level_compact j)). Qed.

(** Source for [circular_disc_level_step_subset]: the
    original G_(n+1) union lies in the original G_n
    union, supporting 3.3.19, p. 302. *)
Lemma circular_disc_level_step_subset j:
  circular_disc_level_union H j.+1 `<=` circular_disc_level_union H j.
Proof.
move=>x [a [ha hx]];rewrite (circular_disc_tree_step hH) in ha.
have [z [k [hz hza]]]:=(@circular_disc_refinement_membership R (H j) (rho j) (j+4)%N a).1 ha.
exists z;split=>//;apply:(@circular_disc_child_containment j z k).
by rewrite -hza.
Qed.

(** Source for [circular_disc_levels_nested]: full original
    nested-level inclusion, supporting 3.3.19, p. 302. *)
Lemma circular_disc_levels_nested i j:(i<=j)%N ->
  circular_disc_level_union H j `<=` circular_disc_level_union H i.
Proof.
move=>hij.
have hEq:(i+(j-i)=j)%N by rewrite subnKC.
rewrite -hEq;elim:(j-i)%N=>[|k ih];first by rewrite addn0;exact:subset_refl.
rewrite addnS;exact:subset_trans (@circular_disc_level_step_subset (i+k)%N) ih.

Qed.

(** Source for [circular_disc_tree_centres_nonempty]: actual
    nonempty original disc families at every level,
    supporting 3.3.19, p. 302. *)
Lemma circular_disc_tree_centres_nonempty j:exists z,z \in H j.
Proof.
elim:j=>[|j [z hz]].
- exists 0%R;by rewrite (circular_disc_tree_root hH) in_fset1 eqxx.
- have hn:(0<j+4)%N by rewrite addn_gt0 orbT.
  pose k:'I_(j+4):=Ordinal hn.
  exists (circular_disc_child_center z (rho j) k).
  rewrite (circular_disc_tree_step hH);apply/circular_disc_refinement_membership.
  by exists z,k;split.
Qed.

(** Source for [circular_disc_level_nonempty]: every actual
    level union is nonempty, supporting 3.3.19, p. 302. *)
Lemma circular_disc_level_nonempty j:circular_disc_level_union H j !=set0.
Proof.
have [z hz]:=@circular_disc_tree_centres_nonempty j;exists z,z;split=>//.
change (is_true (mdist z z<=rho j));rewrite mdistxx;exact:ltW (factorial_disc_radius_positive hs j).
Qed.

(** Source for [circular_disc_limit_nonempty_compact]: the
    original A is a nonempty compact set, 3.3.19, p. 302.
    Actual finite compact levels and their nesting supply
    the intersection; compactness is not a defining law. *)
Theorem circular_disc_limit_nonempty_compact (A:set E):
  is_circular_disc_limit H A ->A!=set0 /\compact A.
Proof.
move=>hA.
have hEq:A=\bigcap_j circular_disc_level_union H j.
  apply/seteqP;split.
  - move=>x hx j _;exact:(hA x).1 hx j.
  - move=>x hx;apply:(hA x).2=>j;exact:hx j Logic.I.
rewrite hEq;split.
- exact:compact_nested_nonempty_intersection (@circular_disc_level_compact 0)
    circular_disc_level_closed circular_disc_levels_nested circular_disc_level_nonempty.
- have hClosed:closed (\bigcap_j circular_disc_level_union H j).
    apply:closed_bigI=>j _;exact:circular_disc_level_closed.
  have hI:(\bigcap_j circular_disc_level_union H j)=
      circular_disc_level_union H 0%N `&` (\bigcap_j circular_disc_level_union H j).
    apply/seteqP;split.
    + move=>x hx;split;[exact:hx 0%N Logic.I|exact hx].
    + by move=>x [_ hx].
  rewrite hI;exact:(compact_closedI (@circular_disc_level_compact 0) hClosed).
Qed.
End Topology.
