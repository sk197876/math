(** Federer (1969), 4.1.22, p. 379, and the
    inclusion diagram of 4.1.24, p. 381: boundary
    preserves the original integral polyhedral classes and
    their real spans, with exactly the same compact K.
    Reuse the original simplex face sum of 4.1.11,
    p. 366, and the independently specified generation laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Bilinear Hom ModuleQuotient TopologicalGroupUP
  RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct InnerConvex ConvexHull
  SmoothCompactSet CurrentSpaces CurrentBoundary
  OrientedSimplexCurrentUP OrientedSimplexFaceIndices PolyhedralCurrentGenerators PolyhedralCurrentAlgebra
  PolyhedralCurrentUnion PolyhedralCurrentFiniteSums OpenSimplexGeometry
  GeneratedAdditiveSubgroupUP GeneratedLinearSubspaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PolyhedralCurrentBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C:=(fun d=>@current_space R h2 n U hU d).
Variable K:smooth_compact_set hNX U.
Local Notation Integral:=(fun d=>@integral_polyhedral_current_class R h2 n d U hU K).
Local Notation Real:=(fun d=>@polyhedral_current_subspace R h2 n d U hU K).
Local Notation bd:=(@current_boundary R h2 n m U hU).

(** Source for [integral_polyhedral_open_simplex_boundary]: the
    alternating integer face sum of each original admissible
    simplex remains in its same compact integral class,
    by 4.1.11, p. 366, for the definitions of
    4.1.22, p. 379, and 4.1.24's inclusion on p. 381. *)
Lemma integral_polyhedral_open_simplex_boundary (v:'I_(m.+2)->X):
  @polyhedral_simplex_vertex_hull R n m.+1 v `<=` smooth_compact_carrier K->
  Integral m (bd (@open_oriented_simplex_current R h2 n m.+1 U hU v)).
Proof.
move=>hHull;rewrite open_simplex_current_boundary.
apply:(@integral_polyhedral_current_finite_sum R h2 n m U hU K (m.+2))=>i.
have hFaceHull:@polyhedral_simplex_vertex_hull R n m (current_simplex_face v i)
    `<=` smooth_compact_carrier K.
  apply:(subset_trans _ hHull).
  apply:convex_hull_least;last exact:convex_hull_convex.
  move=>x [j <-];apply:convex_hull_includes;by exists (lift i j).
have hFace:=@integral_polyhedral_current_generator R h2 n m U hU K
  (current_simplex_face v i) hFaceHull.
have hSigned k:Integral m
    ((-1:R)^+k*:@open_oriented_simplex_current R h2 n m U hU (current_simplex_face v i)).
  elim:k=>[|k ih].
  - by rewrite expr0 scale1r.
  - rewrite exprS mulN1r scaleNr;exact:integral_polyhedral_current_negate ih.
exact:hSigned.
Qed.

(** Source for [integral_polyhedral_current_boundary_supported]:
    the actual boundary of every integral polyhedral current
    is integral polyhedral with the same K. This follows
    from the original generated subgroup in 4.1.22, p. 379,
    and the face identity used by 4.1.24, p. 381. *)
Theorem integral_polyhedral_current_boundary_supported (T:C m.+1):
  Integral m.+1 T->Integral m (bd T).
Proof.
pose Good:=fun S:C m.+1=>Integral m (bd S).
have hGood:is_subgroup (fun S T:C m.+1=>S+T) (fun T=>-T) 0 Good.
  constructor.
  - rewrite /Good (lin0 (hom_linear bd));exact:integral_polyhedral_current_zero.
  - move=>S Q hS hQ;rewrite /Good (linD (hom_linear bd)).
    exact:integral_polyhedral_current_add hS hQ.
  - move=>S hS;rewrite /Good -scaleN1r (linZ (hom_linear bd)) scaleN1r.
    exact:integral_polyhedral_current_negate hS.
apply:(generated_additive_subgroup_least
  (@integral_polyhedral_current_class_laws R h2 n m.+1 U hU K) hGood).
move=>S [v [hHull <-]];exact:integral_polyhedral_open_simplex_boundary hHull.
Qed.

(** Source for [real_polyhedral_current_boundary_supported]:
    the real-span version of the same original boundary
    inclusion, supporting the full diagram of 4.1.24,
    p. 381, from 4.1.22, p. 379. No restriction
    is imposed on real coefficients. *)
Theorem real_polyhedral_current_boundary_supported (T:C m.+1):
  Real m.+1 T->Real m (bd T).
Proof.
pose Good:=fun S:C m.+1=>Real m (bd S).
have hZero:Good 0.
  rewrite /Good (lin0 (hom_linear bd));exact:subspace_zero.
have hAdd:forall S Q:C m.+1,Good S->Good Q->Good (S+Q).
  move=>S Q hS hQ;rewrite /Good (linD (hom_linear bd)).
  exact:subspace_add hS hQ.
have hScale:forall (a:R) (S:C m.+1),Good S->Good (a*:S).
  move=>a S hS;rewrite /Good (linZ (hom_linear bd)).
  exact:(@subspace_scale R (C m)
    (@polyhedral_current_subspace R h2 n m U hU K) a (bd S) hS).
pose GoodSpace:=@Subspace R (C m.+1) Good hZero hAdd hScale.
apply:(generated_linear_subspace_least
  (@polyhedral_current_subspace_laws R h2 n m.+1 U hU K) (W:=GoodSpace)).
move=>S hS;apply:integral_polyhedral_current_is_polyhedral.
exact:integral_polyhedral_current_boundary_supported hS.
Qed.
End PolyhedralCurrentBoundary.
