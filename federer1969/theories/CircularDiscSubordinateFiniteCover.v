(** Federer (1969), 3.3.19, p. 303:
    compactness permits a finite original subcover
    whose remaining members each contain a whole
    disc from one common original fine level. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls FactorialDiscScalesSealed
  CircularDiscTreeUP CircularDiscTreeTopology CircularDiscLimitUP CircularDiscFineCover CompactFiniteCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.

(** Source for [circular_disc_subordinate_finite_cover]:
    both finite-cover reductions in the first paragraph
    of 3.3.19, p. 303. Every
    selected index belongs to the original cover;
    repeated covering sets are retained as original
    indices. No finite-cover or uniform-level premise
    is supplied by the theorem's caller. *)
Theorem circular_disc_subordinate_finite_cover (R:realType)
    (H:nat->{fset (inner_metric_space (@euclidean_inner_productP R 2))})
    (A:set (inner_metric_space (@euclidean_inner_productP R 2)))
    (I:choiceType) (D:set I) (U:I->set (inner_metric_space (@euclidean_inner_productP R 2))):
  is_circular_disc_tree H ->is_circular_disc_limit H A ->
  (forall i,D i ->open (U i)) ->A `<=` \bigcup_(i in D) U i ->
  exists (nu:nat) (G:{fset I}),
    (forall i,i \in G ->D i) /\A `<=` \bigcup_(i in [set` G]) U i /\
    (forall i,i \in G ->exists z,z \in H nu /\
      metric_closed_ball z (@FactorialDiscScales.radius R nu) `<=` U i).
Proof.
move=>hH hA hOpen hCover.
pose E:=inner_metric_space (@euclidean_inner_productP R 2).
have [hNonempty hCompact]:=@circular_disc_limit_nonempty_compact R H hH A hA.
have [F hFD hFCover]:=@compact_open_finite_cover [the topologicalType of E] I D U A
  hCompact hOpen hCover.
have hFSubset i:i \in F ->D i by move=>hi;exact:set_mem (hFD i hi).
have [J hFine]:=@circular_disc_levels_subordinate_open_cover R H hH A hA I [set` F] U
  (fun i hi=>hOpen i (hFSubset i hi)) hFCover.
pose G:{fset I}:=[fset i in F | `[<exists z,z \in H J /\
  metric_closed_ball z (@FactorialDiscScales.radius R J) `<=` U i>]].
have hG i:i \in G <->i \in F /\exists z,z \in H J /\
    metric_closed_ball z (@FactorialDiscScales.radius R J) `<=` U i.
  rewrite /G in_fset /= !inE;split=>[/andP[hi /asboolP hDisc]|[hi hDisc]];first by split.
  apply/andP;split=>//;exact/asboolP.
exists J,G;split.
- move=>i /hG[hi _];exact:hFSubset i hi.
split.
- move=>x hxA;have [z [hz hxZ]]:=(hA x).1 hxA J.
  have [i [hi hInside]]:=hFine J (leqnn J) z hz.
  exists i;last exact:hInside x hxZ.
  apply/hG;split=>//;by exists z;split.
- by move=>i /hG[_ hDisc].
Qed.
