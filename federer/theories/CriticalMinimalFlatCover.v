(** Federer (1969), 3.4.2(7), p. 312: the full minimal-dimension
    base case, with the original relatively closed source. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannSubspaces GrassmannAbbreviations EuclideanInnerProduct
  HilbertFormCompactness NormMetric RealNormUP CriticalManifoldFamilyUP
  CriticalManifoldCompactCover CriticalMinimalCompactPiece CriticalFlatPieceRestriction
  CriticalFlatCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [critical_minimal_dimension_flat_cover_exists]: the
    mu=nu base case of 3.4.2(7), p. 312, after its compact reduction.
    The original relatively closed C is covered exactly by compact
    sets G_j, and every pair (S,G_j) belongs to the original Ψ(S,C,k).
    Both the discrete and positive-dimensional alternatives are proved;
    compactness of C is unnecessary. *)
Theorem critical_minimal_dimension_flat_cover_exists (R:realType) m d
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:G (R_n R m) d) k (S C:set (R_n R m)):
  critical_manifold_family Z (m-d) k S ->
  @is_relatively_closed_source (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) S C ->
  exists T G,is_critical_flat_cover hNY Z (m-d) S C k T G.
Proof.
move=>hFamily hClosed.
have hCS:=relatively_closed_source_subset hClosed.
have [K [hK hUnion]]:=critical_relatively_closed_compact_cover hFamily.2.2.1 hClosed.
exists (fun _=>S),K;constructor;last exact:hUnion.
move=>j.
have hKS:K j `<=` S by move=>x hx;exact:hCS x ((hK j).2 x hx).
have hPiece:=@critical_minimal_dimension_compact_piece R m d Y NY hNY Z k S (K j)
  hFamily hKS (hK j).1.
exact:(critical_flat_piece_larger_zero_set (hK j).2 hPiece).
Qed.
