(** Federer (1969), 4.1.23, p. 380:
    the original ordered scalar rectangle
    is integral polyhedral in its original
    containing convex compact box. Its
    factorial simplex decomposition retains every
    original corner and the full hull
    of each generator, not merely its current support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm InnerConvex HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ConvexHull
  CurrentSpaces CurrentOpenRestrictionIdentity SmoothCompactSet
  OrientedRectangleDomain ScalarSegmentFactors CurrentScalarRectangle
  CurrentScalarRectangleVertex CurrentScalarRectangleDecomposition
  OrientedSimplexCurrentSealed PolyhedralCurrentGenerators PolyhedralCurrentAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ScalarRectanglePolyhedral.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable f : seq (R*R).
Local Notation n := (oriented_rectangle_dimension (@scalar_segment_factors R f)).
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation T := (@current_scalar_rectangle R h2 f).
Variable K : smooth_compact_set hNX Full.
Hypothesis hConvex : is_inner_convex (smooth_compact_carrier K).
Hypothesis hCorners : forall x, @is_current_scalar_rectangle_vertex R f x ->
  smooth_compact_carrier K x.

(** Source for [scalar_rectangle_integral_polyhedral_decomposition]:
    the rectangle in Federer 4.1.23,
    p. 380, is the sum
    of exactly m! original oriented
    simplexes from 4.1.11, p. 366.
    Each full simplex hull lies in
    the original containing box K. *)
Theorem scalar_rectangle_integral_polyhedral_decomposition :
  exists (I : finType) (v : I -> 'I_(n.+1) -> X),
    #|I|=((size f)`!)%N /\
    T=\sum_i @OrientedSimplexCurrent.value R h2 n n (v i) /\
    (forall i j, @is_current_scalar_rectangle_vertex R f (v i j)) /\
    (forall i, @polyhedral_simplex_vertex_hull R n n (v i) `<=`
      smooth_compact_carrier K) /\
    @integral_polyhedral_current_class R h2 n n Full hFull K T.
Proof.
have [I [v [hCount [hSum hVertices]]]] := @current_scalar_rectangle_decomposition R h2 f.
have hHull i : @polyhedral_simplex_vertex_hull R n n (v i) `<=`
    smooth_compact_carrier K.
  apply: convex_hull_least; last exact: hConvex.
  move=> x [j <-]; exact: hCorners (hVertices i j).
have hGenerator i : @integral_polyhedral_current_class R h2 n n Full hFull K
    (@OrientedSimplexCurrent.value R h2 n n (v i)).
  have h := @integral_polyhedral_current_generator R h2 n n Full hFull K (v i) (hHull i).
  by rewrite /open_oriented_simplex_current current_open_restriction_identity in h.
have hIntegral : @integral_polyhedral_current_class R h2 n n Full hFull K T.
  rewrite hSum; elim/big_rec: _=> [|i S hI hS].
  - exact: integral_polyhedral_current_zero.
  - exact: integral_polyhedral_current_add (hGenerator i) hS.
exists I,v; split; first exact: hCount.
split; first exact: hSum.
split; first exact: hVertices.
split; [exact: hHull|exact: hIntegral].
Qed.
End ScalarRectanglePolyhedral.
