(** Federer (1969), 3.3.19, p. 302: all original
    distinct discs at a common level are separated by more
    than their radius. Derive the global assertion from
    actual sibling separation and parent containment. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscRefinement CircularDiscTreeUP CircularDiscTreeTopology CircularDiscSiblingSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Separation.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation hs:=(@FactorialDiscScales.laws R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_tree_separation]: the actual
    strict distance bound between distinct original G_n discs,
    3.3.19, p. 302. Every actual pair of points in their
    closed discs is covered; no separation or selected-parent
    hypothesis is imposed on the original tree. *)
Theorem circular_disc_tree_separation j:
  forall z w:E,z \in H j ->w \in H j ->z!=w ->
  forall x y:E,metric_closed_ball z (rho j) x ->metric_closed_ball w (rho j) y ->
    rho j<mdist x y.
Proof.
elim:j=>[|j ih] z w hz hw hne x y hx hy.
- move:hz hw;rewrite (circular_disc_tree_root hH) !in_fset1=>/eqP hz /eqP hw.
  by move:hne;rewrite hz hw eqxx.
- rewrite (circular_disc_tree_step hH) in hz hw.
  have [a [k [ha hZ]]]:=(@circular_disc_refinement_membership R (H j) (rho j) (j+4)%N z).1 hz.
  have [b [l [hb hW]]]:=(@circular_disc_refinement_membership R (H j) (rho j) (j+4)%N w).1 hw.
  case:(eqVneq a b)=>[hAB|hAB].
  + subst b.
    have hkl:k!=l.
      apply/negP=>/eqP hKL;rewrite hKL in hZ.
      have hZW:z=w by rewrite hZ hW.
      by move:hne;rewrite hZW eqxx.
    have hx':metric_closed_ball (circular_disc_child_center a (rho j) k)
        (rho j/(j+4)%:R) x.
      by rewrite -(factorial_disc_radius_step hs) -hZ.
    have hy':metric_closed_ball (circular_disc_child_center a (rho j) l)
        (rho j/(j+4)%:R) y.
      by rewrite -(factorial_disc_radius_step hs) -hW.
    rewrite (factorial_disc_radius_step hs).
    exact:(@circular_disc_sibling_separation R a (rho j) (j+4)%N k l x y
      (@factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho hs j)
      (leq_addl j 4) hkl hx' hy').
  + have hxA:metric_closed_ball a (rho j) x.
      apply:(@circular_disc_child_containment R j a k);by rewrite -hZ.
    have hyB:metric_closed_ball b (rho j) y.
      apply:(@circular_disc_child_containment R j b l);by rewrite -hW.
    have hOld:=ih a b ha hb hAB x y hxA hyB.
    exact:lt_trans (@factorial_disc_radius_decreases R (@FactorialDiscScales.count R) rho hs j) hOld.
Qed.
End Separation.
