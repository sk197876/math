(** Federer (1969), 3.2.39, p. 275: prove
    existence of the printed finite compact family, retaining
    exact Jacobian mass and nearly full image cost. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry
  CompactJacobianCoreFamily SeparatedCompactCoreCubeCover FiniteUniqueIncidenceImageBound
  FiniteCompactJacobianCoverUP JacobianDensityMeasure LipschitzUP HausdorffMeasure
  MeasureUP MeasureBasic MeasureAlmostBasic MeasureFiniteClosure FiniteNullOverlapAdditivity
  FiniteCoverMeasureBounds TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_compact_jacobian_cover_exists]: the
    complete finite-family consequence cited in Federer 3.2.39,
    p. 275. Actual area and image-cost measures give disjoint
    compact source cores with nearly full image cost. A fine
    coordinate grid meets at most one core in each cell. The
    original compact A intersected with these cells covers A
    exactly; actual null faces preserve the exact Jacobian sum.
    Unique core incidence and the measure cover law retain the
    core image cost. Both printed assertions are proved, rather
    than assumed as a hypothesis of the Minkowski theorem. *)
Theorem finite_compact_jacobian_cover_exists (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (A:set (inner_metric_space (@euclidean_inner_productP R m))) (e:R):
  (0<m)%N ->is_metric_lipschitz setT f ->compact A ->0<e ->
  exists (J:finType) C,is_finite_compact_jacobian_cover f A e (C:J->set (inner_metric_space (@euclidean_inner_productP R m))).
Proof.
move=>hm0 hLip hA he.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R m.
pose nu:=euclidean_jacobian_measure f.
pose hm:=euclidean_lebesgue_is_measure R m.
pose hn:=euclidean_jacobian_measure_is_measure hLip.
pose beta:=@hausdorff_measure R Y m.
have [I [K [hK [hKDisjoint hCoreCost]]]]:=@compact_jacobian_disjoint_core_family_exists R m n f A e hLip hA he.
have [h [J [a [Q [hh [hQ [hCover [hNull hUnique]]]]]]]]:=
  @separated_compact_core_cube_cover_exists R m I A K hm0 hA (fun i=>(hK i).1) hKDisjoint.
pose C j:=A `&` Q j.
have hCompact j:compact (C j).
  exact:compact_closedI hA (compact_closed (@metric_hausdorff R X) (coordinate_cube_compact (hQ j))).
have hSubset j:C j `<=` A by move=>x hx; exact:hx.1.
have hUnion:(\bigcup_j C j)=A.
  apply/seteqP; split=>x.
  - move=>[j _ hx]; exact:hx.1.
  - move=>hx; have [j _ hj]:=hCover x hx; exists j=>//; by split.
have hMeas j:measure_measurable nu (C j).
  apply:(@euclidean_jacobian_measure_measurable R m n f (C j) hLip).
  apply:euclidean_borel_measurable; exact:closed_borel_set (compact_closed (@metric_hausdorff R X) (hCompact j)).
have hPair j k:j!=k ->nu (C j `&` C k)=0%E.
  move=>hjk; apply:euclidean_jacobian_measure_null.
  apply:(@measure_null_subset R X mu hm _ (Q j `&` Q k)) _ (hNull j k hjk).
  by move=>x [[_ hj] [_ hk]]; split.
have hSum:(\sum_j nu (C j))%E=nu A.
  have hAdd:=@measure_finite_family_null_overlap_additivity R X J nu hn C setT
    (@finite_finset J setT) (fun j _=>hMeas j) (fun j k _ _=>hPair j k).
  rewrite (@finite_type_nonnegative_sum R J (fun j=>nu (C j))
    (fun j=>measure_nonnegative hn (C j))) hUnion in hAdd.
  exact:esym hAdd.
have hCoreCover i:K i `<=` \bigcup_j C j.
  move=>x hx; rewrite hUnion; exact:(hK i).2 x hx.
have hCoreUnique j i k:(C j `&` K i)!=set0 ->(C j `&` K k)!=set0 ->i=k.
  move=>[x [[hxA hxQ] hxi]] [y [[hyA hyQ] hyk]].
  have hMeetI:(Q j `&` K i)!=set0 by exists x; split.
  have hMeetK:(Q j `&` K k)!=set0 by exists y; split.
  exact (@hUnique j i k hMeetI hMeetK).
have hCost:=@finite_unique_incidence_image_cost_bound R X Y I J beta f K C
  (@hausdorff_measure_is_measure R Y m) hCoreCover hCoreUnique.
exists J,C; constructor=>//.
exact:le_trans hCoreCost (leeD hCost (lexx e%:E)).
Qed.
