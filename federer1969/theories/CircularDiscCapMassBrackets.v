(** Federer (1969), 3.3.19, p. 305: bracket the
    actual original cap mass by exact selected-child masses.
    Original A, parent, orientation and closed contacts remain. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws CircularTrigonometrySealed
  CircularRegularDirections CircularDiscRefinement CircularDiscTreeUP CircularDiscLimitUP
  CircularDiscParentChildPartition CircularDiscChildSubfamilyMass CircularDiscCaps CircularDiscCapChildCriteria
  HausdorffMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Brackets.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation B:=(@euclidean_inner_product R 2).
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).

(** Source for [circular_disc_cap_meeting_children]: the
    actual original children meeting S(z,rho,u,gamma),
    supporting the upper cap bound in 3.3.19, p. 305. *)
Definition circular_disc_cap_meeting_children j (z u:E) (gamma:R):{fset 'I_(j+4)}:=
  [fset k:'I_(j+4) | `[<exists x:E,
    metric_closed_ball (circular_disc_child_center z (rho j) k) (rho j.+1) x /\
      circular_disc_cap z (rho j) u gamma x>]].

(** Source for [circular_disc_cap_inner_children]: actual
    original child indices whose direction has the proved
    sufficient coordinate margin, supporting the lower cap
    bound in 3.3.19, p. 305. *)
Definition circular_disc_cap_inner_children j (u:E) (gamma:R):{fset 'I_(j+4)}:=
  [fset k:'I_(j+4) | C gamma+2/(j+4)%:R<=B (@circular_regular_direction R (j+4)%N k) u].

(** Source for [circular_disc_cap_meeting_child_coordinate]:
    every actually meeting original child satisfies the actual
    cosine threshold, supporting 3.3.19, p. 305. *)
Lemma circular_disc_cap_meeting_child_coordinate j (z u:E) (gamma:R) (k:'I_(j+4)):
  inner_norm (@euclidean_inner_productP R 2) u= 1 ->
  k \in circular_disc_cap_meeting_children j z u gamma ->
  C gamma-2/(j+4)%:R<=B (@circular_regular_direction R (j+4)%N k) u.
Proof.
move=>hu;rewrite /circular_disc_cap_meeting_children in_fset /= =>/asboolP[x [hx hCap]].
have hr:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho
  (@FactorialDiscScales.laws R) j.
have hn:(0<j+4)%N by rewrite addn_gt0 orbT.
apply:(@circular_disc_child_meeting_cap_cosine R z u (rho j) gamma (j+4)%N k hr hn hu).
exists x;split=>//.
by rewrite -(factorial_disc_radius_step (@FactorialDiscScales.laws R)).
Qed.

(** Source for [circular_disc_cap_inner_child_subset]: each
    actual selected inner child lies wholly in the original
    cap, supporting the lower bound of 3.3.19, p. 305. *)
Lemma circular_disc_cap_inner_child_subset j (z u:E) (gamma:R) (k:'I_(j+4)):
  inner_norm (@euclidean_inner_productP R 2) u= 1 ->
  k \in circular_disc_cap_inner_children j u gamma ->
  metric_closed_ball (circular_disc_child_center z (rho j) k) (rho j.+1) `<=`
    circular_disc_cap z (rho j) u gamma.
Proof.
move=>hu;rewrite /circular_disc_cap_inner_children in_fset /= =>hCoordinate.
have hr:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho
  (@FactorialDiscScales.laws R) j.
have hn:(0<j+4)%N by rewrite addn_gt0 orbT.
rewrite (factorial_disc_radius_step (@FactorialDiscScales.laws R)).
exact:(@circular_disc_child_inside_cap_cosine R z u (rho j) gamma (j+4)%N k hr hn hu hCoordinate).
Qed.

Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_original_cap_mass_brackets]:
    the actual original H1 cap mass lies between
    2 rho_n times the contained-child count and
    2 rho_n times the meeting-child count. Actual
    parent/child partition, original subset inclusions and
    exact piece masses prove both bounds in the uniform
    cap comparison of 3.3.19, p. 305. *)
Theorem circular_disc_original_cap_mass_brackets j (z u:E) (gamma:R):
  z \in H j ->inner_norm (@euclidean_inner_productP R 2) u= 1 ->
  ((2* rho j.+1*#|` circular_disc_cap_inner_children j u gamma|%:R)%:E<=
    mu (A `&` circular_disc_cap z (rho j) u gamma))%E /\
  (mu (A `&` circular_disc_cap z (rho j) u gamma)<=
    (2* rho j.+1*#|` circular_disc_cap_meeting_children j z u gamma|%:R)%:E)%E.
Proof.
move=>hz hu.
have hMu:= @hausdorff_measure_is_measure R E 1.
pose F:= circular_disc_cap_inner_children j u gamma.
pose G:= circular_disc_cap_meeting_children j z u gamma.
pose D:= fun k:'I_(j+4)=>metric_closed_ball (circular_disc_child_center z (rho j) k) (rho j.+1).
have hLowerSubset:(A `&` (\bigcup_(k in [set` F]) D k)) `<=`
    (A `&` circular_disc_cap z (rho j) u gamma).
  move=>x [hxA [k hk hx]];split=>//.
  exact:(@circular_disc_cap_inner_child_subset j z u gamma k hu hk x hx).
have hUpperSubset:(A `&` circular_disc_cap z (rho j) u gamma) `<=`
    (A `&` (\bigcup_(k in [set` G]) D k)).
  move=>x [hxA hxCap];split=>//.
  have hxParent:(A `&` metric_closed_ball z (rho j)) x by split=>//;exact:hxCap.1.
  rewrite (@circular_disc_parent_child_partition R H hH A hA j z hz) in hxParent.
  have [k _ [_ hx]]:= hxParent.
  have hkG:k \in G.
    rewrite /G /circular_disc_cap_meeting_children in_fset /=;apply/asboolP.
    by exists x;split.
  by exists k.
have hLower:= @measure_mono R E mu hMu _ _ hLowerSubset.
have hUpper:= @measure_mono R E mu hMu _ _ hUpperSubset.
rewrite (@circular_disc_child_subfamily_mass R H hH A hA j z F hz) in hLower.
rewrite (@circular_disc_child_subfamily_mass R H hH A hA j z G hz) in hUpper.
by split.
Qed.
End Brackets.
