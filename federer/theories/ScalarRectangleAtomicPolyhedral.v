(** Federer (1969), 4.1.23, p. 380:
    each rectangle at a transverse atom
    is the original sum of m!
    integral simplexes. Consequently R times Q
    lies in the real polyhedral class,
    with every full simplex hull in
    the same containing coordinate box. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom Bilinear ModuleQuotient RealNormUP NormDifferentialUP
  NormOpenDomainLaws InnerNorm InnerConvex HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates
  EuclideanCartesianMap ConvexHull CurrentSpaces CurrentDirac SmoothCompactSet
  CurrentDegreeTransport CurrentAmbientCartesianProduct
  CurrentAmbientRightPointProduct CurrentAmbientProductFiniteSums
  OrientedRectangleDomain ScalarSegmentFactors CurrentScalarRectangle
  CurrentScalarRectangleVertex CurrentScalarRectangleDecomposition
  OrientedSimplexCurrentSealed PolyhedralCurrentGenerators PolyhedralCurrentAlgebra
  CurrentOpenRestrictionIdentity PositiveAtomicZeroCurrentMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AtomicRectanglePolyhedral.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable f : seq (R*R).
Local Notation m := (oriented_rectangle_dimension (@scalar_segment_factors R f)).
Variable n : nat.
Local Notation Full := (fun d : nat => fun _ : R_n R d => True).
Local Notation hFull := (fun (d : nat) (x : R_n R d) (_ : True) =>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Local Notation Rectangle := (@current_scalar_rectangle R h2 f).
Local Notation Product := (@current_ambient_cartesian_product R h2 m n m 0%N).
Local Notation Tr := (@current_degree_transport R h2 (m+n) (Full (m+n)) (hFull (m+n))
  (m+0) m (addn0 m)).
Local Notation Point := (@dirac_current R h2 n (Full n) (hFull n)).
Variable K : smooth_compact_set hNZ (Full (m+n)).
Hypothesis hConvex : is_inner_convex (smooth_compact_carrier K).

(** Source for [scalar_rectangle_point_slice_decomposition]:
    the actual R times [b_k] is
    a sum of precisely m! integral
    m-simplexes, each with original rectangle
    corners at that fixed transverse atom,
    Federer 4.1.23, p. 380.
    The full hull of each generator
    lies in the original box K. *)
Theorem scalar_rectangle_point_slice_decomposition (b : R_n R n)
    (hCorners : forall x, @is_current_scalar_rectangle_vertex R f x ->
      smooth_compact_carrier K (@euclidean_block_join R m n (x,b))) :
  exists (J : finType) (v : J -> 'I_(m.+1) -> R_n R (m+n)),
    #|J|=((size f)`!)%N /\
    Tr (Product Rectangle (Point b))=
      \sum_j @OrientedSimplexCurrent.value R h2 (m+n) m (v j) /\
    (forall j l, exists x, @is_current_scalar_rectangle_vertex R f x /\
      v j l=@euclidean_block_join R m n (x,b)) /\
    (forall j, @polyhedral_simplex_vertex_hull R (m+n) m (v j) `<=`
      smooth_compact_carrier K) /\
    @integral_polyhedral_current_class R h2 (m+n) m (Full (m+n)) (hFull (m+n)) K
      (Tr (Product Rectangle (Point b))).
Proof.
have [J [w [hCount [hRectangle hVertices]]]] := @current_scalar_rectangle_decomposition R h2 f.
pose simplex := fun j : J => @OrientedSimplexCurrent.value R h2 m m (w j).
pose v := fun (j : J) l => @euclidean_block_join R m n (w j l,b).
have hWeighted : Rectangle=\sum_j (1:R)*:simplex j.
  rewrite hRectangle; apply: eq_bigr=> j _; by rewrite scale1r.
have hSum : Tr (Product Rectangle (Point b))=
    \sum_j @OrientedSimplexCurrent.value R h2 (m+n) m (v j).
  rewrite hWeighted current_ambient_product_first_weighted_sum linear_sum.
  apply: eq_bigr=> j _; rewrite scale1r.
  exact: (@current_ambient_right_point_simplex R h2 m n b m (w j)).
have hHull j : @polyhedral_simplex_vertex_hull R (m+n) m (v j) `<=`
    smooth_compact_carrier K.
  apply: convex_hull_least; last exact: hConvex.
  move=> x [l <-]; exact: hCorners (hVertices j l).
have hGenerator j : @integral_polyhedral_current_class R h2 (m+n) m
    (Full (m+n)) (hFull (m+n)) K
    (@OrientedSimplexCurrent.value R h2 (m+n) m (v j)).
  have h := @integral_polyhedral_current_generator R h2 (m+n) m
    (Full (m+n)) (hFull (m+n)) K (v j) (hHull j).
  by rewrite /open_oriented_simplex_current current_open_restriction_identity in h.
have hIntegral : @integral_polyhedral_current_class R h2 (m+n) m
    (Full (m+n)) (hFull (m+n)) K (Tr (Product Rectangle (Point b))).
  rewrite hSum; elim/big_rec: _=> [|j S hI hS].
  - exact: integral_polyhedral_current_zero.
  - exact: integral_polyhedral_current_add (hGenerator j) hS.
exists J,v; split; first exact: hCount.
split; first exact: hSum.
split.
- move=> j l; exists (w j l); split; [exact: hVertices|reflexivity].
- split; [exact: hHull|exact: hIntegral].
Qed.

(** Source for [scalar_rectangle_atomic_product_polyhedral]:
    P=R times Q belongs to the
    original real polyhedral class in
    the same compact box, Federer
    4.1.23, p. 380. Every
    real weight is permitted algebraically;
    positivity is used separately for the
    exact mass assertion. *)
Theorem scalar_rectangle_atomic_product_polyhedral (I : finType)
    (tag : I -> R_n R n) (a : I -> R)
    (hCorners : forall i x, @is_current_scalar_rectangle_vertex R f x ->
      smooth_compact_carrier K (@euclidean_block_join R m n (x,tag i))) :
  @polyhedral_current_subspace R h2 (m+n) m (Full (m+n)) (hFull (m+n)) K
    (Tr (Product Rectangle (@positive_atomic_zero_current R h2 n I tag a))).
Proof.
pose Real := @polyhedral_current_subspace R h2 (m+n) m
  (Full (m+n)) (hFull (m+n)) K.
have hSlices i : Real (Tr (Product Rectangle (Point (tag i)))).
  have [_ [_ [_ [_ [_ [_ hIntegral]]]]]] :=
    scalar_rectangle_point_slice_decomposition (hCorners i).
  exact: integral_polyhedral_current_is_polyhedral hIntegral.
rewrite /positive_atomic_zero_current current_ambient_product_second_weighted_sum linear_sum.
have hSum : (\sum_i Tr (a i*:Product Rectangle (Point (tag i))))=
    \sum_i a i*:Tr (Product Rectangle (Point (tag i))).
  apply: eq_bigr=> i _; exact: (linZ (hom_linear Tr) (a i) _).
rewrite hSum; elim/big_rec: _=> [|i S hI hS].
- exact: subspace_zero.
- apply: subspace_add; last exact: hS.
  exact: (@subspace_scale R _ Real (a i)
    (Tr (Product Rectangle (Point (tag i)))) (hSlices i)).
Qed.
End AtomicRectanglePolyhedral.
