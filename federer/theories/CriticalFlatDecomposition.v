(** Federer (1969), 3.4.2(7), pp. 311–314: the full
    decomposition into compact flat pieces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannSubspaces GrassmannAbbreviations EuclideanInnerProduct
  HilbertFormCompactness NormMetric RealNormUP EuclideanProjectionSpace CriticalManifoldFamilyUP
  CriticalManifoldCompactCover CriticalFlatPiecesUP CriticalFlatCoverUP
  CriticalMinimalFlatCover CriticalFlatCompactReduction CriticalCommonFlatCovers
  CriticalOutsideFlatCover CriticalFlatCoverAssembly.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [critical_flat_cover_exists]: the complete assertion
    3.4.2(7), p. 311, proved on pp. 312–314. The original
    relatively closed C has a sequence of compact-manifold pairs
    in Ψ(S,C,k) covering exactly C. The same pairs work for every
    original class-k function vanishing on C. Simultaneous induction
    on dimension and class discharges both lower-induction calls.
    No cover, flatness estimate, target basis, or extra closedness
    condition is a numbered-statement hypothesis. *)
Theorem critical_flat_cover_exists (R:realType) m d
    (Z:G (R_n R m) d) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY):
  forall mu k (S C:set (R_n R m)),critical_manifold_family Z mu k S ->
    @is_relatively_closed_source (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m))) S C ->
    exists T G,is_critical_flat_cover hNY Z mu S C k T G.
Proof.
elim=>[|mu hDimensionInduction].
- move=>k S C hFamily hClosed.
  have hZero:(m-d)%N=0%N by apply/eqP;rewrite -leqn0;exact:hFamily.1.
  have hMinimal:critical_manifold_family Z (m-d) k S by rewrite hZero.
  have [T [G hCover]]:=@critical_minimal_dimension_flat_cover_exists R m d Y NY hNY Z k S C hMinimal hClosed.
  exists T,G;by rewrite hZero in hCover.
- elim=>[|k hClassInduction] S C hFamily hClosed.
  + have hBad:(0<0)%N:=hFamily.2.1;by [].
  + case:(eqVneq (m-d)%N mu.+1)=>[hEqual|hDifferent].
    * have hMinimal:critical_manifold_family Z (m-d) k.+1 S by rewrite hEqual.
      have [T [G hCover]]:=@critical_minimal_dimension_flat_cover_exists R m d Y NY hNY Z k.+1 S C hMinimal hClosed.
      exists T,G;by rewrite hEqual in hCover.
    * have hSmaller:(m-d<=mu)%N.
        have hStrict:(m-d<mu.+1)%N by rewrite ltn_neqAle hDifferent hFamily.1.
        exact:hStrict.
      apply:(@critical_flat_cover_compact_reduction R m d Z mu.+1 k.+1 Y NY hNY S C
        hFamily hClosed).
      move=>K hKS hCompact.
      have [p [g hChart]]:exists (p:euclidean_projection_space R m mu.+1) g,
          is_critical_manifold_chart k.+1 (grassmann_val Z) S p g.
        case:hFamily.2.2.2=>[hImpossible|hChart];last exact:hChart.
        by [].
      have [TO [GO [hOutside hOutsideUnion]]]:=
        @critical_outside_flat_cover R m d Z mu k.+1 Y NY hNY S K p g
          hFamily hChart hSmaller hKS hCompact
          (fun V hV hVC=>hDimensionInduction k.+1 V (V `&` K) hV hVC).
      have [TB [GB [hCommon hCommonUnion]]]:exists T G:nat->set (R_n R m),
          (forall j,is_critical_flat_piece hNY Z mu.+1 S K k.+1 (T j) (G j)) /\
          critical_common_tangent_zero_set hNY (grassmann_val Z) S K k.+1=\bigcup_j G j.
        case:(eqVneq k 0%N)=>[hkZero|hkNonzero].
        - subst k;exact:(@critical_class_one_common_flat_cover R m d Z mu.+1 Y NY hNY
            S K p g hFamily hChart hKS hCompact).
        - have hk:(1<=k)%N by rewrite lt0n hkNonzero.
          exact:(@critical_higher_common_flat_cover R m d Z mu.+1 k Y NY hNY S K p g
            hk hFamily hChart hKS hCompact
            (fun B hS hB=>hClassInduction S B hS hB)).
      pose B:=critical_common_tangent_zero_set hNY (grassmann_val Z) S K k.+1.
      have hUnion:B `|` (K `\` B)=K.
        apply/seteqP;split.
        - move=>x [hx|hx];[exact:hx.1|exact:hx.1].
        - move=>x hx;case:(pselect (B x))=>[hB|hNo];[by left|right;by split].
      have [T [G [hPieces hCover]]]:=@critical_two_flat_covers R m d Z mu.+1 Y NY hNY
        S K B (K `\` B) k.+1 TB GB TO GO hCommon hCommonUnion hOutside hOutsideUnion.
      rewrite hUnion in hCover;exists T,G;by constructor.
Qed.
