(** Federer (1969), 4.1.11, p. 366: the
    cyclically ordered triangle [w,u,v] equals [u,v,w].
    Apply two of the already proved original vertex
    transpositions. Repeated vertices remain allowed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals fingroup perm.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct Biorthogonal
  CurrentSpaces CurrentSimplexFirstSwap OrientedSimplexCurrentSealed
  OrientedSimplexFirstSwap OrientedSimplexTranspositions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [oriented_simplex_triangle_cycle]: the
    printed [v_3,v_1,v_2]=[v_1,v_2,v_3] in
    the triangle-image argument, Federer 4.1.11,
    p. 366. The identity holds for all vertices
    in every Euclidean ambient space. *)
Lemma oriented_simplex_triangle_cycle (R:realType) (h2:(1+1:R)!=0) n (u v w:R_n R n):
  @OrientedSimplexCurrent.value R h2 n 2%N
    (ordinal_cons w (ordinal_cons u (fun _:'I_1=>v)))=
  @OrientedSimplexCurrent.value R h2 n 2%N
    (ordinal_cons u (ordinal_cons v (fun _:'I_1=>w))).
Proof.
pose V:=ordinal_cons u (ordinal_cons v (fun _:'I_1=>w)).
pose i0:=(ord0:'I_3).
pose i1:=(lift ord0 (ord0:'I_2):'I_3).
pose i2:=(lift ord0 (lift ord0 (ord0:'I_1)):'I_3).
have h01:i0!=i1:=neq_lift _ _.
have h02:i0!=i2:=neq_lift _ _.
have h12:i1!=i2.
  by rewrite /i1 /i2 (inj_eq (@lift_inj 3%N ord0)) neq_lift.
pose W:=fun k:'I_3=>V (tperm i1 i2 k).
have hShape:current_simplex_first_swap W=ordinal_cons w (ordinal_cons u (fun _:'I_1=>v)).
  apply:funext=>k;case:(unliftP ord0 k)=>[r ->|->].
  - case:(unliftP ord0 r)=>[q ->|->].
    + rewrite (ord1 q) current_simplex_first_swap_rest /W.
      rewrite (tpermR i1 i2) /V !ordinal_consS !ordinal_cons0.
      by [].
    + rewrite current_simplex_first_swap_second /W.
      have h10:i1!=i0 by rewrite eq_sym.
      have h20:i2!=i0 by rewrite eq_sym.
      rewrite (tpermD h10 h20) /V ordinal_cons0 ordinal_consS ordinal_cons0.
      by [].
  - rewrite current_simplex_first_swap_head /W (tpermL i1 i2) /V
      !ordinal_consS !ordinal_cons0.
    by [].
have hFirst:=@oriented_simplex_current_first_swap R h2 1%N n W.
have hSecond:=@oriented_simplex_current_transposition R h2 n 2%N i1 i2 h12 V.
by rewrite hShape hSecond opprK in hFirst.
Qed.
