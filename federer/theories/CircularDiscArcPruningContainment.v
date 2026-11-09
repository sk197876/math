(** Federer (1969), 3.3.19, p. 305: the local
    exceptional-stage families contain exactly original disc
    centres, and every original point avoiding the arc
    remains in all selected stage unions. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls FactorialDiscScalesSealed
  CircularDiscRefinement CircularDiscTreeUP CircularDiscTreeTopology CircularDiscLimitUP CircularDiscLevelPieces
  CircularDiscRadialMapUP CircularDiscRadialIntervals CircularDiscBadChildCount
  CircularDiscArcPruningUP CircularDiscArcPruningExistence PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Containment.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_arc_pruned_step_subset]: every
    selected exceptional child is an actual original next-level
    disc, supporting K_n subset G_n in 3.3.19, p. 305. *)
Lemma circular_disc_arc_pruned_step_subset j (eta:partial_function E E) (F:{fset E}) (a b:R):
  (F `<=` H j)%fset ->(@circular_disc_arc_pruned_step R j eta F a b `<=` H j.+1)%fset.
Proof.
move=>hF;apply/fsubsetP=>w /circular_disc_arc_pruned_step_membership[z [k [hz [hk ->]]]].
rewrite (circular_disc_tree_step hH);apply/circular_disc_refinement_membership.
exists z,k;split=>//;exact:(fsubsetP hF z hz).
Qed.

(** Source for [circular_disc_arc_pruning_subset]: all K_n
    are subfamilies of their actual original levels G_n,
    supporting the mass estimates in 3.3.19, p. 305. *)
Theorem circular_disc_arc_pruning_subset (eta:nat->partial_function E E) s (a b:R)
    (K:nat->{fset E}):is_circular_disc_arc_pruning H eta s a b K ->
  forall l,(K l `<=` H (s+l)%N)%fset.
Proof.
move=>hK;elim=>[|l ih].
- rewrite (circular_arc_pruning_root hK) addn0.
  apply/fsubsetP=>z hz;exact hz.
- rewrite addnS (circular_arc_pruning_step hK).
  exact:(@circular_disc_arc_pruned_step_subset (s+l)%N (eta (s+l)%N) (K l) a b ih).
Qed.

(** Source for [circular_disc_arc_pruning_contains_avoiders]:
    the actual original A-points whose every late eta_n value
    avoids the arc belong to every original exceptional-stage
    union, exactly the inclusion before the nullity conclusion
    in 3.3.19, p. 305. Actual next-level and unique
    parent membership discharge the recursion. *)
Theorem circular_disc_arc_pruning_contains_avoiders (eta:nat->partial_function E E)
    (hEta:forall j,is_circular_disc_radial_map H j (eta j)) s (a b:R)
    (K:nat->{fset E}) (hK:is_circular_disc_arc_pruning H eta s a b K)
    (A:set E) (hA:is_circular_disc_limit H A) (x:E):
  A x ->(forall l v,partial_function_graph (eta (s+l)%N) x v ->~circular_parameter_arc a b v) ->
  forall l,exists z:E,z \in K l /\metric_closed_ball z (rho (s+l)%N) x.
Proof.
move=>hxA hAvoid;elim=>[|l [u [hu hxU]]].
- rewrite (circular_arc_pruning_root hK) addn0;exact:(hA x).1 hxA s.
- have hSubset:=@circular_disc_arc_pruning_subset eta s a b K hK l.
  have huH:=fsubsetP hSubset u hu.
  have [w [hw hxW]]:=(hA x).1 hxA (s+l).+1.
  have hwOriginal:=hw.
  rewrite (circular_disc_tree_step hH) in hw.
  have [z [k [hz hW]]]:=(@circular_disc_refinement_membership R (H (s+l)%N)
    (rho (s+l)%N) ((s+l)+4)%N w).1 hw.
  have hxChild:metric_closed_ball (circular_disc_child_center z (rho (s+l)%N) k)
    (rho (s+l).+1) x by rewrite -hW.
  have hxZ:=@circular_disc_child_containment R (s+l)%N z k x hxChild.
  have hEqual:=@circular_disc_level_point_unique R H hH (s+l)%N x u z huH hz hxU hxZ.
  have hzK:z \in K l by rewrite -hEqual.
  have hxDomain:partial_function_domain (eta (s+l)%N) x.
    apply:(circular_radial_map_domain (hEta (s+l)%N) x).2.
    by exists w;split.
  have [v hGraph]:=hxDomain.
  have hBad:k \in @circular_disc_bad_child_indices R (s+l)%N (eta (s+l)%N) z a b.
    rewrite /circular_disc_bad_child_indices in_fset /=;apply/asboolP.
    exists x,v;split=>//;split=>//;exact:hAvoid l v hGraph.
  exists w;rewrite addnS;split=>//.
  rewrite (circular_arc_pruning_step hK);apply/circular_disc_arc_pruned_step_membership.
  by exists z,k;split=>//;split.
Qed.
End Containment.
