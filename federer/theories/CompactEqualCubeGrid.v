(** Federer (1969), 3.2.38, p. 274: choose a finite equal-side
    coordinate grid covering a compact source at any prescribed mesh. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanAdditiveGroup EqualCoordinateCubeGridUP EqualCoordinateCubeGridLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_equal_cube_grid_encloses]: supporting finite
    family F in Federer 3.2.38, p. 274. At every positive side h
    an actual finite equal grid covers C. A coordinate bound and
    Archimedean enlargement discharge existence; empty C and dimension
    zero remain. Subsequent filtering keeps just cells meeting C. *)
Theorem compact_equal_cube_grid_encloses (R:realType) n
    (C:set (inner_metric_space (@euclidean_inner_productP R n))) (h:R):
  compact C ->0<h ->exists k (a:R_n R n) Q,
    is_equal_coordinate_cube_grid k a h Q /\C `<=` \bigcup_s Q s.
Proof.
move=>hC hh.
have [B [hB hCoordinates]]:=euclidean_compact_coordinate_bound hC.
have hQuotient:0<=2*B/h.
  apply:divr_ge0; [exact:mulr_ge0 (ler0n R 2) hB|exact:ltW hh].
pose k:=Num.bound (2*B/h).
have hArch:2*B/h<k%:R by exact:archi_boundP.
have hkR:(0<(k%:R:R))%R:=le_lt_trans hQuotient hArch.
have hk:(0<k)%N by move:hkR; rewrite ltr0n.
have hWidth:2*B<k%:R*h by move:hArch; rewrite ltr_pdivrMr.
pose a:R_n R n:=[ffun _=> -B].
have [Q hQ]:=equal_coordinate_cube_grid_exists a hk (ltW hh).
exists k,a,Q; split=>// x hx.
have hBox:forall i,a i<=x i<=a i+k%:R*h.
  move=>i; rewrite ffunE; have hi:=hCoordinates x hx i.
  rewrite ler_norml in hi; have /andP[hl hu]:=hi; apply/andP; split; lra.
have [s hs]:=equal_coordinate_grid_covers_box hQ hBox.
by exists s.
Qed.
