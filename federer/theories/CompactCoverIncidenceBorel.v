(** Federer (1969), 3.4.8(5), p. 328:
    projecting a countable compact incidence set into
    O(n) gives a Borel set. Metric open conditions are
    exhausted by closed sets, so the original nonzero
    tests remain part of the incidence condition. *)
From mathcomp Require Import all_boot all_order boolp classical_sets cardinality reals topology.
From Federer Require Import IncreasingCompactCoverUP MetricOpenClosedCover
  TopologicalProductMaps TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_cover_incidence_borel]: the compact
    projection argument for the original A_j and B_j
    in 3.4.8(5), p. 328. The parameter space is
    compact Hausdorff; the germ witnesses have a proved
    compact cover. The target incidence has one closed
    condition and one open metric condition. *)
Theorem compact_cover_incidence_borel (R:realType)
    (T U:topologicalType) (Z:pseudoMetricType R)
    (S:set T) (K:nat->set T) (F:T*U->Z) (Q V:set Z):
  is_increasing_compact_cover S K ->compact [set:U] ->hausdorff_space U ->
  continuous F ->closed Q ->open V ->
  borel_set [set y:U|exists x:T,S x /\Q (F (x,y)) /\V (F (x,y))].
Proof.
move=>hK hU hHausdorff hF hQ hV.
have [C [hC hCover]]:=@metric_open_countable_closed_cover R Z V hV.
pose D i j:set (T*U):=(K i `*` setT) `&` (F @^-1` (Q `&` C j)).
have hDCompact i j:compact (D i j).
  apply:compact_closedI.
  - exact:(compact_setX (@increasing_compact_cover_compact T S K hK i) hU).
  - apply:(@preimage_closed (T*U)%type Z F (Q `&` C j)).
    + by move=>p _;exact:hF p.
    + exact:(closedI hQ (hC j).1).
have hBorel i j:borel_set ((@snd T U) @` D i j).
  apply:closed_borel_set;apply:(compact_closed hHausdorff).
  apply:continuous_compact;last exact:hDCompact i j.
  exact:continuous_subspaceT (@second_projection_continuous T U).
have hExact:[set y:U|exists x:T,S x /\Q (F (x,y)) /\V (F (x,y))]=
    \bigcup_i (\bigcup_j ((@snd T U) @` D i j)).
  apply/seteqP;split.
  - move=>y [x [hx [hClosed hOpen]]].
    have [i hi]:=@increasing_compact_cover_covers T S K hK x hx.
    have hCovers:(\bigcup_j C j) (F (x,y)) by rewrite -hCover.
    have [j _ hj]:=hCovers.
    exists i;first exact:Logic.I.
    exists j;first exact:Logic.I.
    exists (x,y);last reflexivity.
    by split;first split;last split.
  - move=>y [i _ [j _ [p hp hEqual]]].
    case:p hp hEqual=>x z [[hx _] [hClosed hCj]] /= hEqual.
    change (z=y) in hEqual;subst z.
    exists x;split.
    + exact:(@increasing_compact_cover_contained T S K hK i x hx).
    + split;first exact:hClosed.
      exact:(hC j).2 (F (x,y)) hCj.
rewrite hExact.
apply:(@borel_set_countable_union U nat setT _ (countableP (@setT nat)))=>i _.
apply:(@borel_set_countable_union U nat setT _ (countableP (@setT nat)))=>j _.
exact:hBorel.
Qed.
