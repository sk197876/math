(** Federer (1969), 3.3.19, p. 302: the
    original circular child family has no more than
    n/2+1 closed discs meeting any closed halfplane
    whose boundary passes through the original parent centre.
    Prove the count for every actual orientation. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric
  RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed CircularUnitVectors
  CircularUnitVectorSurjection CircularAngleLift CyclicGridShiftSeparation CyclicGridArcCount
  CircularHalfplaneAngle CircularDiscHalfplaneCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Count.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_disc_halfplane_subfamily_bound]:
    every subfamily of original children meeting a closed
    halfplane has 2 card(F)<=n+2, the unrounded
    n/2+1 count in 3.3.19, p. 302. Original
    odd n, tangencies, parent centre and radius remain. *)
Theorem circular_disc_halfplane_subfamily_bound (z u:E) (r:R) n (F:{fset 'I_n}):
  0<r ->(4<=n)%N ->inner_norm (@euclidean_inner_productP R 2) u= 1 ->
  (forall k,k \in F ->circular_child_meets_halfplane z u r k) ->
  (2*#|` F|<=n+2)%N.
Proof.
move=>hr hn hu hHit.
have hp:=real_trigonometry_pi_positive hb.
have [t [ht0 [ht2 hT]]]:=@circular_unit_vector_surjective R u hu.
have [v [hpv [hvp hV]]]:=@circular_angle_central_representative R t ht0 ht2.
have hDirection:circular_unit_vector v=u by rewrite hV hT.
have hnP:(0<n)%N:=leq_trans (erefl true : (1<=4)%N) hn.
have hNP:(0<n%:R:>R) by rewrite ltr0n.
have hNN:(n%:R:R)!= 0 by rewrite gt_eqF.
pose q:R:=2* p/n%:R.
pose a:R:=p/2+p/(2* n%:R).
pose b:'I_n->bool:=circular_angle_lift_branch v.
have hq:0<q by rewrite /q divr_gt0 // mulr_gt0 // ltr0n.
have hBudget:q* n%:R= 2* p by rewrite /q divfK.
have hQuarter:p/(2* n%:R)=q/4 by rewrite /q invfM;nra.
have ha:0<a by rewrite /a hQuarter;nra.
have hWidth:(v+a)-(v-a)<=((n%:R+1)/2)* q by rewrite /a hQuarter;nra.
apply:(@cyclic_grid_arc_count R q n b F (v-a) (v+a) hq _ hWidth).
- lra.
- move=>k hk.
  have hOriginal:circular_child_meets_halfplane z (circular_unit_vector v) r k.
    by rewrite hDirection;exact:hHit k hk.
  have hCos:=@circular_disc_halfplane_cosine_bound R z r n k v hr hn hOriginal.
  have hLiftCos:=@circular_angle_lift_cosine R n v k hnP.
  have [hLower hUpper]:=@circular_angle_lift_bounds R n v k hnP hpv hvp.
  rewrite -hLiftCos in hCos.
  have [hArcLower hArcUpper]:=@circular_halfplane_angle_interval R n
    (cyclic_grid_shifted_point q b k-v) hn hLower hUpper hCos.
  change (is_true (v-a<cyclic_grid_shifted_point q b k) /\
    is_true (cyclic_grid_shifted_point q b k<v+a)).
  split;rewrite /a;lra.
Qed.

(** Source for [circular_halfplane_child_indices]: the
    actual original child indices whose closed discs
    meet the original closed halfplane, 3.3.19, p. 302. *)
Definition circular_halfplane_child_indices (z u:E) (r:R) n:{fset 'I_n}:=
  [fset k:'I_n | `[<circular_child_meets_halfplane z u r k>]].

(** Source for [circular_disc_halfplane_count]: literal
    actual count of all original children meeting the
    original closed halfplane, 3.3.19, p. 302.
    The independent centre-injectivity theorem identifies
    these indices with distinct original discs. *)
Corollary circular_disc_halfplane_count (z u:E) (r:R) n:
  0<r ->(4<=n)%N ->inner_norm (@euclidean_inner_productP R 2) u= 1 ->
  (2*#|` circular_halfplane_child_indices z u r n|<=n+2)%N.
Proof.
move=>hr hn hu;apply:(@circular_disc_halfplane_subfamily_bound z u r n
  (circular_halfplane_child_indices z u r n) hr hn hu)=>k.
by rewrite /circular_halfplane_child_indices in_fset /= =>/asboolP.
Qed.
End Count.
