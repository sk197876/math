(** Federer (1969), 3.4.12, p. 339: the local complex sheets
    give exactly the original fixed number of points in each fibre.
    Apply the independent covering laws and the existing finite ordinal
    enumeration, including degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormMetric ScalarRestriction ComplexScalarSealed
  HolomorphicFiniteCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
(** Source for [holomorphic_finite_cover_fibre_enumeration]: the actual
    local sheet values enumerate the original fibre uniquely, with the
    exact degree, 3.4.12, p. 339. *)
Theorem holomorphic_finite_cover_fibre_enumeration (R:realType)
    (X Y:lmodType (ComplexScalars.C R)) (NX:X->R) (NY:Y->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
    (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (Z:set (real_norm_metric_space hNX)) (V:set (real_norm_metric_space hNY))
    (P:Hom X Y) k:
  @is_finite_holomorphic_projection_cover R X Y NX NY hNX hNY Z V P k ->
  forall y,V y ->exists roots:seq X,uniq roots /\size roots=k /\
    forall x,Z x /\P x=y <->x \in roots.
Proof.
move=>hCover y hy.
have [W [s [hOpen [hWy [hWV [hHolomorphic [hInverse [hDisjoint [hWhole hImages]]]]]]]]]:=
  holomorphic_cover_local_branches hCover hy.
pose roots:=map (fun i:'I_k=>s i y) (enum 'I_k).
have hInjective:injective (fun i:'I_k=>s i y).
  move=>i j hEqual;exact:(@hDisjoint i j y hWy hEqual).
exists roots;split.
- by rewrite /roots (map_inj_uniq hInjective) enum_uniq.
- split;first by rewrite /roots size_map size_enum_ord.
  move=>x;split.
  + move=>[hX hPx].
    have hWPx:W (P x) by rewrite hPx.
    have [i [_ hValue]]:=(hWhole x).1 (conj hX hWPx).
    apply/mapP;exists i;first by rewrite mem_enum.
    by rewrite -hPx hValue.
  + move/mapP=>[i hi hValue];rewrite hValue;exact:(@hInverse i y hWy).
Qed.
