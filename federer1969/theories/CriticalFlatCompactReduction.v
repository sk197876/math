(** Federer (1969), 3.4.2(7), p. 312: compact source
    exhaustion reduces the full assertion to its compact case. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannSubspaces GrassmannAbbreviations EuclideanInnerProduct
  HilbertFormCompactness NormMetric RealNormUP CriticalManifoldFamilyUP
  CriticalManifoldCompactCover CriticalFlatPiecesUP CriticalFlatCoverUP
  CriticalFlatPieceRestriction CriticalFlatCoverAssembly.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [critical_flat_cover_compact_reduction]: the first
    reduction in the proof of 3.4.2(7), p. 312. Exhaust the
    original relatively closed C by contained compact sets. A
    compact-case cover controls all functions vanishing on its
    compact set, hence every original function vanishing on C.
    Flatten the covers while preserving their compact-manifold pairs. *)
Theorem critical_flat_cover_compact_reduction (R:realType) m d
    (Z:G (R_n R m) d) mu k (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (S C:set (R_n R m)):
  critical_manifold_family Z mu k S ->
  @is_relatively_closed_source (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) S C ->
  (forall K:set (R_n R m),K `<=` S ->
    @compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m))) K ->
    exists T G,is_critical_flat_cover hNY Z mu S K k T G) ->
  exists T G,is_critical_flat_cover hNY Z mu S C k T G.
Proof.
move=>hFamily hClosed hCompactCase.
have hCS:=relatively_closed_source_subset hClosed.
have [K [hK hUnion]]:=critical_relatively_closed_compact_cover hFamily.2.2.1 hClosed.
have hRows i:exists row:((nat->set (R_n R m))*(nat->set (R_n R m)))%type,
    is_critical_flat_cover hNY Z mu S (K i) k row.1 row.2.
  have hKS:K i `<=` S by move=>x hx;exact:hCS x ((hK i).2 x hx).
  have [T [G hCover]]:=hCompactCase (K i) hKS (hK i).1.
  by exists (T,G).
have [row hRow]:=choice hRows.
have hPieces i j:is_critical_flat_piece hNY Z mu S C k ((row i).1 j) ((row i).2 j).
  exact:(critical_flat_piece_larger_zero_set (hK i).2 (critical_flat_cover_pieces (hRow i) j)).
have hDouble:C=\bigcup_i \bigcup_j (row i).2 j.
  apply/seteqP;split.
  - move=>x hx;rewrite hUnion in hx;have [i _ hi]:=hx.
    exists i;first exact:I.
    by rewrite -(critical_flat_cover_union (hRow i)).
  - move=>x [i _ [j _ hj]].
    have hKi:K i x.
      rewrite (critical_flat_cover_union (hRow i));by exists j.
    exact:(hK i).2 x hKi.
have [T [G [hAll hCover]]]:=@critical_double_flat_cover R m d Z mu Y NY hNY S C C k
  (fun i=>(row i).1) (fun i=>(row i).2) hPieces hDouble.
exists T,G;by constructor.
Qed.
