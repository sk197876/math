(** Federer (1969), 4.1.11, p. 366: the first
    two vertices may be exchanged at the cost of a
    minus sign. Follow the printed induction: identify
    top-dimensional currents from their boundaries, then
    transfer through an actual affine parametrisation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom AffineMaps RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanAffineSmooth
  CurrentSpaces CurrentCompactCurrentArithmetic CurrentCompactPushforwardAlgebra CurrentCompactMapNegation
  CurrentCartesianMapPullback CurrentSimplexFrame CurrentSimplexFirstSwap
  OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws OrientedSimplexCurrentAffine
  OrientedSimplexFirstSwapBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section OrientedSimplexFirstSwap.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.

(** Source for [oriented_simplex_current_first_swap]: the
    original [u_1,u_0,u_2,...]=- [u_0,u_1,u_2,...],
    Federer 4.1.11, p. 366. The target simplex may be
    degenerate and its ambient dimension is arbitrary. *)
Theorem oriented_simplex_current_first_swap m:
  forall n (v:'I_(m.+2)->R_n R n),
    @OrientedSimplexCurrent.value R h2 n m.+1 (current_simplex_first_swap v)=
      -@OrientedSimplexCurrent.value R h2 n m.+1 v.
Proof.
elim:m=>[|m ih] n v;first exact:(@oriented_simplex_first_swap_pair R h2 n v).
pose d:=m.+2.
pose X:=R_n R d;pose Y:=R_n R n.
pose U:=fun _:X=>True;pose V:=fun _:Y=>True.
pose hU:=fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R d)) x.
pose hV:=fun (y:Y) (_:True)=>@norm_full_domain_interior R Y
  (inner_norm (@euclidean_inner_productP R n)) y.
pose w:=@current_standard_simplex_vertices R d.
have[A [hA hVertices]]:=@current_simplex_affine_vertices_exists R d n w v
  (@current_standard_simplex_nondegenerate R d).
pose AImage:=fun (x:X) (_:U x)=>Logic.I.
pose AGlobal:=@euclidean_affine_map_smooth R d n U hU A hA.
pose AClass:=@current_cartesian_factor_open_class R d n U hU A AGlobal.
pose S:=@OrientedSimplexCurrent.value R h2 d d w.
pose Swapped:=@OrientedSimplexCurrent.value R h2 d d (current_simplex_first_swap w).
pose hS:=@oriented_simplex_current_compact R h2 d d w.
pose hSwapped:=@oriented_simplex_current_compact R h2 d d (current_simplex_first_swap w).
have hTop:Swapped= -S:=@oriented_simplex_first_swap_top R h2 d m ih (erefl d) w.
have hNegative:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
    (@current_support R h2 d U hU d (-S)).
  have h:=@current_compact_scaled_support R h2 d d U hU S (-1:R) hS.
  by rewrite scaleN1r in h.
have hInput:=@current_compact_map_pushforward_congruence R h2 d n U V hU hV
  A AImage AClass d Swapped (-S) hSwapped hNegative hTop.
have hNegativeImage:=@current_compact_map_negative_image R h2 d n U V hU hV
  A AImage AClass d S hS hNegative.
have hImage:=@oriented_simplex_current_affine R h2 d n A hA d w hS.
have hSwappedImage:=@oriented_simplex_current_affine R h2 d n A hA d
  (current_simplex_first_swap w) hSwapped.
have hOriginalVertices:(fun k=>A (w k))=v by apply:funext=>k;exact:hVertices.
have hSwappedVertices:(fun k=>A (current_simplex_first_swap w k))=current_simplex_first_swap v.
  apply:funext=>k;exact:hVertices.
rewrite hOriginalVertices in hImage.
rewrite hSwappedVertices in hSwappedImage.
exact:(eq_trans (esym hSwappedImage) (eq_trans hInput
  (eq_trans hNegativeImage (congr1 (fun T=>-T) hImage)))).
Qed.
End OrientedSimplexFirstSwap.
