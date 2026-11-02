(** Federer (1969), 3.2.39, p. 275: a fine
    finite coordinate grid separates disjoint compact source cores. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology ring lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry CompactEqualCubeGrid FiniteMeetingCubeCover
  FiniteCompactTubeSeparation MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [separated_compact_core_cube_cover_exists]: expand
    the finite closed-family selection in Federer 3.2.39,
    p. 275. Uniform separation of finitely many disjoint
    compact cores permits a prescribed fine equal cube grid.
    Every cell meets at most one core. Actual null coordinate
    faces, source coverage and all cube laws are proved by
    the earlier grid lemmas, without a source partition premise.
    Positive source degree is used only for this mesh division. *)
Theorem separated_compact_core_cube_cover_exists (R:realType) m (I:finType)
    (A:set (inner_metric_space (@euclidean_inner_productP R m)))
    (K:I->set (inner_metric_space (@euclidean_inner_productP R m))):
  (0<m)%N ->compact A ->(forall i,compact (K i)) ->
  (forall i j,i!=j ->K i `&` K j=set0) ->
  exists (h:R) (J:finType) (a:J->R_n R m)
    (Q:J->set (inner_metric_space (@euclidean_inner_productP R m))),
    0<h /\(forall j,is_euclidean_coordinate_cube (a j) h (Q j)) /\
    A `<=` \bigcup_j Q j /\
    (forall j k,j!=k ->@euclidean_lebesgue_measure R m (Q j `&` Q k)=0%E) /\
    forall j i k,(Q j `&` K i)!=set0 ->(Q j `&` K k)!=set0 ->i=k.
Proof.
move=>hm0 hA hK hDisjoint.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose F:{fset I}:=[fset i in enum I].
have hF i:i \in F by rewrite /F in_fset mem_enum.
have hNone i j:i \in F ->j \in F ->i!=j ->forall x,K i x ->K j x ->False.
  move=>_ _ hij x hi hj; have hBoth:(K i `&` K j) x by split.
  by rewrite (hDisjoint i j hij) in hBoth.
have [d [hd hTubes]]:=@finite_compact_open_tubes_separated R X I F K
  (fun i _=>hK i) hNone.
pose r:=d/2.
pose h:=d/(4* m%:R).
have hM:0<(m%:R:R) by rewrite ltr0n.
have hr:0<r by rewrite /r divr_gt0 // ltr0n.
have hSmall:r<d by rewrite /r ltr_pdivrMr ?ltr0n // mulr_natr mulr2n ltrDl.
have hSide:0<h by rewrite /h divr_gt0 // mulr_gt0 // ltr0n.
have hMNe:(m%:R:R)!=0 by rewrite gt_eqF.
have hFour:(4:R)!=0 by rewrite pnatr_eq0.
have hDiameter:m%:R*h=d/4 by rewrite /h; field; exact hMNe.
have hMesh:m%:R*h<r by rewrite hDiameter /r; lra.
have [k [corner [P [hP hCover]]]]:=@compact_equal_cube_grid_encloses R m A h hA hSide.
have [J [a [Q [hQ hMeet hSource hNull]]]]:=@finite_meeting_coordinate_grid_cover R m k corner h P A hP hCover.
exists h,J,a,Q; split=>//; split=>//; split=>//; split=>// j i t hQi hQt.
case:(eqVneq i t)=>[hEqual|hNe]; first exact hEqual.
exfalso.
have [x [hx hxi]]:=hQi.
have [y [hy hyt]]:=hQt.
have hXY:mdist x y<r:=le_lt_trans (coordinate_cube_distance_bound (hQ j) hx hy) hMesh.
have hLeft:metric_open_thickening (K i) r y by exists x.
have hRight:metric_open_thickening (K t) r y.
  exists y; first exact hyt.
  change (is_true (@mdist R X y y<r)); by rewrite mdistxx.
exact:(hTubes r ltac:(by apply/andP) i t (hF i) (hF t) hNe y hLeft hRight).
Qed.
