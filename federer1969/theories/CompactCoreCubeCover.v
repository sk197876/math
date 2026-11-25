(** Federer (1969), 3.2.38, pp. 274--275: construct the
    finite good/bad source cover and prove all its actual mass errors. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanCoordinateCubeUP CompactEqualCubeGrid FiniteMeetingCubeCover FiniteCoreFamilySplit
  CompactCoreCubeCoverUP CompactEuclideanTubeExcess FiniteCubeFamilyNearSet MetricOpenThickening
  MeasureUP MeasureBasic MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_core_cube_cover_exists]: supporting finite
    families and final mass errors of Federer 3.2.38, pp. 274--275.
    Actual compact-source open-tube approximation gives one common
    mesh cutoff for C and E. The finite equal grid is filtered to
    cells meeting C and split into cells meeting E and missing E.
    Injective index inclusions preserve null coordinate faces.
    All good-core and bad-parent mass errors are proved, with the
    empty-source, empty-core and zero-dimensional boundaries retained. *)
Theorem compact_core_cube_cover_exists (R:realType) m
    (C E:set (inner_metric_space (@euclidean_inner_productP R m))) (e:R):
  compact C ->compact E ->0<e ->(@euclidean_lebesgue_measure R m (C `\` E)<e%:E)%E ->
  exists d:R,0<d /\forall h:R,0<h ->m%:R*h<d ->
    exists (G B:finType) (aG:G->R_n R m) (aB:B->R_n R m) QG QB,
      is_compact_core_cube_cover C E h e aG aB QG QB.
Proof.
move=>hC hE he hHole.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
have [dC [hdC hOutsideC]]:=compact_euclidean_tube_excess_small hC he.
have [dE [hdE hOutsideE]]:=compact_euclidean_tube_excess_small hE he.
exists (Num.min dC dE); split; first by rewrite lt_min hdC hdE.
move=>h hh hMesh.
have hMinC:Num.min dC dE<=dC by rewrite ge_min lexx.
have hMinE:Num.min dC dE<=dE by rewrite ge_min lexx orbT.
have hMeshC:m%:R*h<dC:=lt_le_trans hMesh hMinC.
have hMeshE:m%:R*h<dE:=lt_le_trans hMesh hMinE.
have [k [a [P [hP hGridCover]]]]:=compact_equal_cube_grid_encloses hC hh.
have [I [aF [QF [hQF hMeetC hCoverC hNullF]]]]:=finite_meeting_coordinate_grid_cover hP hGridCover.
have [G [B [good [bad [hGoodInj hBadInj hMeetE hAvoidE hSplit]]]]]:=
  finite_core_family_split_exists QF E.
pose QG (i:G):=QF (good i).
pose QB (i:B):=QF (bad i).
pose DF:=\bigcup_i QF i.
pose UG:=\bigcup_i QG i.
pose UB:=\bigcup_i QB i.
have hFullNear:DF `<=`metric_open_thickening C dC.
  exact:(@coordinate_cube_family_near_set R m I aF h dC QF C hQF hMeetC hMeshC).
have hGoodNear:UG `<=`metric_open_thickening E dE.
  exact:(@coordinate_cube_family_near_set R m G (fun i=>aF (good i)) h dE QG E
    (fun i=>hQF (good i)) hMeetE hMeshE).
have hOutsideFull:(mu (DF `\` C)<e%:E)%E.
  apply:le_lt_trans _ hOutsideC; apply:(@measure_mono R X mu hm)=>x [hx hn].
  split=>//; exact:hFullNear x hx.
have hGoodOutside:(mu (UG `\` E)<=e%:E)%E.
  apply:le_trans _ (ltW hOutsideE); apply:(@measure_mono R X mu hm)=>x [hx hn].
  split=>//; exact:hGoodNear x hx.
have hGoodSubset:UG `<=` DF by move=>x [i _ hx]; exists (good i).
have hBadSubset:UB `<=` DF by move=>x [i _ hx]; exists (bad i).
have hBadCover:UB `<=` (C `\` E) `|` (DF `\` C).
  move=>x hx; case:(pselect (C x))=>hCx.
  - left; split=>// hEx; have [i _ hxi]:=hx.
    have hFalse:(QB i `&` E) x by split.
    by rewrite (hAvoidE i) in hFalse.
  - right; split=>//; exact:hBadSubset x hx.
have hBadMass:(mu UB<=(2*e)%R%:E)%E.
  apply:le_trans (measure_binary_cover hm hBadCover) _.
  have hSum:=leeD (ltW hHole) (ltW hOutsideFull).
  have hTwo:e+e= 2*e by ring.
  by rewrite -EFinD hTwo in hSum.
have hGoodMass:(mu UG<=mu C+e%:E)%E.
  apply:le_trans (measure_mono hm hGoodSubset) _.
  have hFullCover:DF `<=` C `|` (DF `\` C).
    move=>x hx; case:(pselect (C x))=>hCx; [by left|right; by split].
  apply:le_trans (measure_binary_cover hm hFullCover) _.
  exact:leeD (lexx _) (ltW hOutsideFull).
exists G,B,(fun i=>aF (good i)),(fun i=>aF (bad i)),QG,QB; constructor.
- by move=>i; exact:hQF.
- by move=>i; exact:hQF.
- by rewrite -hSplit; exact:hCoverC.
- exact hMeetE.
- exact hAvoidE.
- move=>i j hij; apply:hNullF.
  apply/eqP=>hEqual; apply:(elimN eqP hij); exact:hGoodInj hEqual.
- move=>i j hij; apply:hNullF.
  apply/eqP=>hEqual; apply:(elimN eqP hij); exact:hBadInj hEqual.
- exact hGoodOutside.
- exact hBadMass.
- exact hGoodMass.
Qed.
