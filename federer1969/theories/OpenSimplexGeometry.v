(** Earlier source scope: Federer (1969), 4.1.22, p. 379,
    uses the actual simplex currents of 4.1.11, pp. 365–366.
    Their fixed-index normality gives the original inclusion
    diagram in 4.1.24, p. 381. The retained source comments
    also identify their later use in 4.1.32. These prerequisites use the original public simplex operations. *)
(** Federer (1969), 4.1.32, pp. 392–393:
    simplexes contained in the original open U retain
    their actual normality, support and boundary faces.
    These are laws of the previously defined open
    restriction abbreviation from 4.1.22, p. 379;
    no second simplex family is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces CurrentBoundary CurrentSupportGeometry
  CurrentOpenRestriction CurrentOpenRestrictionSupport CurrentOpenRestrictionBoundary
  CurrentOpenRestrictionNormal NormalCurrentsUP FlatCurrentsUP FlatCurrentFinite
  CurrentNormalOriginalFlat SmoothCompactSet OrientedSimplexCurrentUP
  OrientedSimplexCurrentSealed
  OrientedSimplexCurrentLaws OrientedSimplexFaceIndices OrientedSimplexCurrentBoundary
  OrientedSimplexNormal OrientedSimplexHullSupport PolyhedralCurrentGenerators.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section OpenSimplexGeometry.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation Open:=(fun m v=>@open_oriented_simplex_current R h2 n m U hU v).
Local Notation Support:=(fun m=>@current_support R h2 n U hU m).

(** Source for [open_simplex_current_hull_support]: the
    original simplex current on U is carried by
    its full vertex hull, used in 4.1.32,
    pp. 392–393. This support inclusion needs no
    premise that the whole hull lies in U. *)
Theorem open_simplex_current_hull_support m (v:'I_(m.+1)->X):
  Support m (Open m v) `<=` @polyhedral_simplex_vertex_hull R n m v.
Proof.
apply:(subset_trans (@current_open_restriction_support_subset R h2 n m
  U Full hU hFull (fun x hx=>I) (@OrientedSimplexCurrent.value R h2 n m v))).
exact:oriented_simplex_current_hull_support.
Qed.

(** Source for [open_simplex_current_normal]: the
    original admissible simplex is normal on U,
    supporting the projective and halfspace proofs in
    4.1.32, pp. 392–393. The full original
    hull condition supplies a neighbourhood of support. *)
Theorem open_simplex_current_normal m (v:'I_(m.+1)->X):
  @polyhedral_simplex_vertex_hull R n m v `<=` U->
  @is_normal_current R h2 n U hU m (Open m v).
Proof.
move=>hHull.
apply:(@current_normal_neighbourhood_restriction R h2 n U Full hU hFull
  (fun x hx=>I) m (@OrientedSimplexCurrent.value R h2 n m v)).
- exact:oriented_simplex_current_normal.
- move=>x hx;exact:(hHull x (@oriented_simplex_current_hull_support R h2 n m v x hx)).
Qed.

(** Source for [open_simplex_current_flat]: each
    original admissible simplex on U belongs to
    the compact flat union used in 4.1.32,
    p. 392. No new current is chosen. *)
Theorem open_simplex_current_flat m (v:'I_(m.+1)->X):
  @polyhedral_simplex_vertex_hull R n m v `<=` U->
  @is_flat_current R h2 n m U hU (Open m v).
Proof.
move=>hHull;apply:current_normal_original_flat.
exact:open_simplex_current_normal hHull.
Qed.

(** Source for [open_simplex_current_flat_fixed]: the
    generator lies in the exact original compact
    flat class of its admissible K, supporting
    4.1.32, pp. 392–393. No enlargement or
    replacement of the compact index is needed. *)
Theorem open_simplex_current_flat_fixed m (v:'I_(m.+1)->X)
    (K:smooth_compact_set hNX U):
  @polyhedral_simplex_vertex_hull R n m v `<=` smooth_compact_carrier K->
  @is_flat_current_supported_in R h2 n m U hU K (Open m v).
Proof.
move=>hHull;apply:supported_normal_current_is_flat;split.
- apply:open_simplex_current_normal.
  exact:subset_trans hHull (smooth_compact_in_domain K).
- move=>x hx;exact:(hHull x (@open_simplex_current_hull_support m v x hx)).
Qed.

(** Source for [open_simplex_current_boundary]: the
    original alternating face sum on U, used by
    the induction in 4.1.32, p. 392.
    Restriction commutes with the actual boundary and
    every term of the already proved finite sum. *)
Theorem open_simplex_current_boundary m (v:'I_(m.+2)->X):
  @current_boundary R h2 n m U hU (Open m.+1 v)=
    \sum_(k:'I_(m.+2)) (-1:R)^+(k:nat)*:Open m (current_simplex_face v k).
Proof.
rewrite /open_oriented_simplex_current -current_open_restriction_boundary
  oriented_simplex_current_boundary linear_sum.
apply:eq_bigr=>k _;exact:linearZ.
Qed.
End OpenSimplexGeometry.
