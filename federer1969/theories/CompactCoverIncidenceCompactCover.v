(** Supporting the stronger auxiliary sentence in Federer (1969),
    3.4.8(5), p. 328: retain the actual compact images of the existing
    incidence proof instead of retaining only their Borel consequence.
    The original metric open test is exhausted by closed subsets. *)
From mathcomp Require Import all_boot all_order boolp classical_sets reals topology.
From Federer Require Import IncreasingCompactCoverUP MetricOpenClosedCover TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_cover_incidence_compact_cover]: the compact
    projection argument in the proof of Federer 3.4.8(5), p. 328,
    with its compact witnesses retained. Finite rectangular unions
    give an increasing cover, so no difference of sigma-compact sets
    is used. *)
Theorem compact_cover_incidence_compact_cover (R:realType)
    (T U:topologicalType) (Z:pseudoMetricType R)
    (S:set T) (K:nat->set T) (F:T*U->Z) (Q V:set Z):
  is_increasing_compact_cover S K ->compact [set:U] ->
  continuous F ->closed Q ->open V ->
  exists L:nat->set U,is_increasing_compact_cover
    [set y:U|exists x:T,S x /\Q (F (x,y)) /\V (F (x,y))] L.
Proof.
move=>hK hU hF hQ hV.
have [C [hC hCover]]:=@metric_open_countable_closed_cover R Z V hV.
pose D i j:set (T*U):=(K i `*` setT) `&` (F @^-1` (Q `&` C j)).
pose P i j:=(@snd T U) @` D i j.
have hCompact i j:compact (P i j).
  apply:continuous_compact;first exact:continuous_subspaceT (@second_projection_continuous T U).
  apply:compact_closedI.
  - exact:(compact_setX (@increasing_compact_cover_compact T S K hK i) hU).
  - apply:(@preimage_closed (T*U)%type Z F (Q `&` C j));first by move=>p _;exact:hF p.
    exact:closedI hQ (hC j).1.
pose L n:set U:=\bigcup_(i<n) (\bigcup_(j<n) P i j).
exists L;constructor.
- move=>n;rewrite /L bigcup_mkord;apply:bigsetU_compact=>i _.
  rewrite bigcup_mkord;apply:bigsetU_compact=>j _;exact:hCompact.
- move=>n y [i hi [j hj [[x z] [[hx _] [hClosed hOpen]] hEqual]]].
  change (z = y) in hEqual;subst z.
  exists x;split;first exact:(increasing_compact_cover_contained hK hx).
  split;first exact:hClosed.
  exact:(hC j).2 (F (x,y)) hOpen.
- move=>m n hMN y [i hi [j hj hY]].
  exists i;first exact:leq_trans hi hMN.
  exists j;first exact:leq_trans hj hMN.
  exact:hY.
- move=>y [x [hX [hClosed hOpen]]].
  have [i hI]:=increasing_compact_cover_covers hK hX.
  have hOpenCover:(\bigcup_j C j) (F (x,y)) by rewrite -hCover.
  have [j _ hJ]:=hOpenCover.
  exists (maxn i j).+1.
  exists i;first exact:leq_ltn_trans (leq_maxl i j) (ltnSn (maxn i j)).
  exists j;first exact:leq_ltn_trans (leq_maxr i j) (ltnSn (maxn i j)).
  exists (x,y);last reflexivity.
  by split;first split;last split.
Qed.
