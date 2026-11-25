(** Federer (1969), 3.3.19, p. 302: the
    exact attained minimum distance between ALL distinct
    discs at every original level, including different
    parents. The strict radius comparison is a consequence. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology ring.
From Federer Require Import CircularTrigonometrySealed EuclideanInnerProduct InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscRefinement CircularDiscTreeUP CircularDiscTreeTopology
  CircularDiscTreeSeparation CircularDiscTreeExactCount CircularDiscMinimumGap CircularDiscLevelMinimumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Minimum.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation N:=(@FactorialDiscScales.count R).
Local Notation hs:=(@FactorialDiscScales.laws R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_tree_minimum_gap]: literal
    attained global gap 2 rho_n ((n-1)sin(pi/n)-1)
    in 3.3.19, p. 302, with book level n=j+4.
    Distinct-parent pairs and every actual point in the
    original closed discs are included. *)
Theorem circular_disc_tree_minimum_gap j:
  is_disc_level_minimum_gap (H j.+1) (rho j.+1)
    (circular_disc_gap (rho j) (j+4)%N).
Proof.
have hPositive:=@factorial_disc_radius_positive R N rho hs j.
have hN4:(4<=j+4)%N:=leq_addl j 4.
have hGapBounds:=@circular_disc_gap_bounds R (rho j) (j+4)%N hPositive hN4.
split.
- move=>z w hz hw hZW x y hx hy.
  rewrite (circular_disc_tree_step hH) in hz hw.
  have [a [k [ha hZ]]]:=(@circular_disc_refinement_membership R (H j) (rho j) (j+4)%N z).1 hz.
  have [b [l [hb hW]]]:=(@circular_disc_refinement_membership R (H j) (rho j) (j+4)%N w).1 hw.
  case:(eqVneq a b)=>[hAB|hAB].
  + subst b;have hKL:k!=l.
      apply/negP=>/eqP hEq;rewrite hEq in hZ.
      have hEqual:z=w by rewrite hZ hW.
      by move:hZW;rewrite hEqual eqxx.
    have hx':metric_closed_ball (circular_disc_child_center a (rho j) k)
        (rho j/(j+4)%:R) x by rewrite -(factorial_disc_radius_step hs) -hZ.
    have hy':metric_closed_ball (circular_disc_child_center a (rho j) l)
        (rho j/(j+4)%:R) y by rewrite -(factorial_disc_radius_step hs) -hW.
    exact:(@circular_disc_sibling_gap_lower R a (rho j) (j+4)%N k l x y
      hPositive hN4 hKL hx' hy').
  + have hxA:metric_closed_ball a (rho j) x.
      apply:(@circular_disc_child_containment R j a k);by rewrite -hZ.
    have hyB:metric_closed_ball b (rho j) y.
      apply:(@circular_disc_child_containment R j b l);by rewrite -hW.
    have hOld:=@circular_disc_tree_separation R H hH j a b ha hb hAB x y hxA hyB.
    exact:le_trans hGapBounds.2 (ltW hOld).
- have [a ha]:=@circular_disc_tree_centres_nonempty R H hH j.
  have [k [l [hKL [x [y [hx [hy hXY]]]]]]]:=
    @circular_disc_sibling_gap_attained R a (rho j) (j+4)%N hPositive hN4.
  pose z:=circular_disc_child_center a (rho j) k.
  pose w:=circular_disc_child_center a (rho j) l.
  have hz:z \in H j.+1.
    rewrite (circular_disc_tree_step hH);apply/circular_disc_refinement_membership.
    by exists a,k;split.
  have hw:w \in H j.+1.
    rewrite (circular_disc_tree_step hH);apply/circular_disc_refinement_membership.
    by exists a,l;split.
  have hZW:z!=w.
    apply/negP=>/eqP hEq.
    have hEqual:=@circular_disc_child_center_injective R a (rho j) (j+4)%N
      hPositive hN4 k l hEq.
    by move:hKL;rewrite hEqual eqxx.
  exists z,w;split=>//;split=>//;split=>//;exists x,y.
  rewrite (factorial_disc_radius_step hs);by split=>//;split.
Qed.

(** Source for [circular_disc_tree_printed_minimum]:
    the displayed original minimum and its strict lower
    radius bound, 3.3.19, p. 302. The independently
    specified actual radius, not an auxiliary bound, occurs. *)
Corollary circular_disc_tree_printed_minimum j:
  is_disc_level_minimum_gap (H j.+1) (rho j.+1)
    (2* rho j.+1*((j+4)%:R-1)*(@CircularTrigonometry.sine R)
      ((@CircularTrigonometry.half_period R)/(j+4)%:R)-2* rho j.+1) /\
  rho j.+1<circular_disc_gap (rho j) (j+4)%N.
Proof.
have hEq:circular_disc_gap (rho j) (j+4)%N=
    2* rho j.+1*((j+4)%:R-1)*(@CircularTrigonometry.sine R)
      ((@CircularTrigonometry.half_period R)/(j+4)%:R)-2* rho j.+1.
  rewrite (factorial_disc_radius_step hs) /circular_disc_gap;ring.
split;first by rewrite -hEq;exact:circular_disc_tree_minimum_gap.
rewrite (factorial_disc_radius_step hs).
exact:(@circular_disc_gap_bounds R (rho j) (j+4)%N
  (@factorial_disc_radius_positive R N rho hs j) (leq_addl j 4)).1.
Qed.
End Minimum.
