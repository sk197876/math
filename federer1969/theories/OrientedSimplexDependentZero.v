(** Earlier mathematical use: Federer (1969), 4.1.27, p. 384,
    the degenerate simplex case in the original cube-current
    identity. Reuse the prepared lower-dimensional support proof;
    the retained locators also describe its later use in 4.1.32. *)
(** Federer (1969), 4.1.32, pp. 392–393:
    dependent simplex vertices give the zero actual
    current, by 4.1.15's lower-dimensional support law.
    This supplies the degenerate cases without changing
    the printed hypotheses on genuine simplexes.
    The same supporting degeneracy statement is used in
    4.1.27, p. 384. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AffineSubspaceSpace CurrentSpaces CurrentSupportGeometry FlatCurrentsUP
  CurrentSimplexFrame OrientedSimplexCurrentSealed OrientedSimplexNormal
  OrientedSimplexHullSupport PolyhedralCurrentGenerators DegenerateSimplexPlane
  CurrentFlatAffinePlaneSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [oriented_simplex_current_dependent_zero]:
    every degenerate original simplex is zero,
    supporting the six propositions of Federer
    4.1.32, pp. 392–393. The proof uses
    the old current support-dimension theorem. *)
Theorem oriented_simplex_current_dependent_zero (R:realType)
    (h2:(1+1:R)!=0) n m (v:'I_(m.+1)->R_n R n):
  ~is_nondegenerate_current_simplex v->
    @OrientedSimplexCurrent.value R h2 n m v=0.
Proof.
move=>hDegenerate.
have[d [A [hd [hA hHull]]]]:=@degenerate_simplex_plane_exists R n m v hDegenerate.
apply:(@current_flat_affine_plane_support_zero R h2 n d m hd
  (fun _=>True)
  (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
    (inner_norm (@euclidean_inner_productP R n)) x) A hA
  (@OrientedSimplexCurrent.value R h2 n m v)
  (@oriented_simplex_current_flat R h2 n m v)).
exact:(subset_trans (@oriented_simplex_current_hull_support R h2 n m v) hHull).
Qed.

(** Source for [open_simplex_current_dependent_zero]:
    the same degenerate actual simplex is zero on
    every original open U, supporting 4.1.32,
    pp. 392–393. No hull-in-U premise is needed. *)
Theorem open_simplex_current_dependent_zero (R:realType)
    (h2:(1+1:R)!=0) n m (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (v:'I_(m.+1)->R_n R n):
  ~is_nondegenerate_current_simplex v->
    @open_oriented_simplex_current R h2 n m U hU v=0.
Proof.
move=>hDegenerate.
by rewrite /open_oriented_simplex_current
  (@oriented_simplex_current_dependent_zero R h2 n m v hDegenerate) linear0.
Qed.
