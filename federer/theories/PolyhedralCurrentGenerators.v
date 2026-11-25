(** Federer (1969), 4.1.22, p. 379: the fixed-K
    generators are the original oriented m-simplexes whose full
    vertex convex hull lies in K. Use the validated opaque
    simplex family of 4.1.11, p. 365, and the already defined
    open restriction of actual currents. Degenerate vertices and
    degrees above the ambient dimension remain allowed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDirac SmoothCompactSet ConvexHull CurrentDensityUP CurrentOpenRestriction
  OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PolyhedralCurrentGenerators.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm
  (@euclidean_inner_productP R n)).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation C := (@current_space R h2 n U hU m).

(** Source for [polyhedral_simplex_vertex_hull]: the convex
    hull of {u_0,...,u_m}, exactly the compact-index condition
    in Federer 4.1.22, p. 379. This is the existing opaque
    convex hull, not a new barycentric construction. *)
Definition polyhedral_simplex_vertex_hull (v:'I_(m.+1)->X):set X:=
  convex_hull [set x|exists i,v i=x].

(** Source for [open_oriented_simplex_current]: the original
    oriented simplex considered as a current on U, supporting
    Federer 4.1.22, p. 379. This abbreviation applies the
    existing open restriction to the validated actual simplex;
    it introduces no new choice witness. *)
Definition open_oriented_simplex_current (v:'I_(m.+1)->X):C:=
  @current_open_restriction R h2 n m U Full hU hFull (fun x hx=>I)
    (@OrientedSimplexCurrent.value R h2 n m v).

(** Source for [polyhedral_simplex_generators]: the exact
    original generator family for the integral fixed-K subgroup,
    Federer 4.1.22, p. 379. Requiring the full hull in K
    is retained even when the simplex current degenerates to zero. *)
Definition polyhedral_simplex_generators (K:smooth_compact_set hNX U):set C:=
  [set T|exists v:'I_(m.+1)->X,
    polyhedral_simplex_vertex_hull v `<=` smooth_compact_carrier K /\
    open_oriented_simplex_current v=T].

(** Source for [polyhedral_simplex_generator]: every original
    admissible oriented simplex is a generator, exactly as in
    the first definition of Federer 4.1.22, p. 379. *)
Lemma polyhedral_simplex_generator (K:smooth_compact_set hNX U)
    (v:'I_(m.+1)->X):
  polyhedral_simplex_vertex_hull v `<=` smooth_compact_carrier K->
  polyhedral_simplex_generators K (open_oriented_simplex_current v).
Proof. move=>hHull;exists v;by split. Qed.

(** Source for [polyhedral_simplex_vertices_in_index]: the
    original full-hull condition places every vertex in K and U,
    supporting Federer 4.1.22, p. 379. No nondegeneracy or
    positive ambient dimension is assumed. *)
Lemma polyhedral_simplex_vertices_in_index (K:smooth_compact_set hNX U)
    (v:'I_(m.+1)->X):
  polyhedral_simplex_vertex_hull v `<=` smooth_compact_carrier K->
  forall i,smooth_compact_carrier K (v i) /\U (v i).
Proof.
move=>hHull i.
have hVertex:polyhedral_simplex_vertex_hull v (v i).
  apply:convex_hull_includes;exists i;by [].
have hK:=hHull (v i) hVertex.
split;first exact:hK.
exact:smooth_compact_in_domain K (v i) hK.
Qed.

(** Source for [polyhedral_simplex_generators_monotone]:
    enlarging the compact index retains each original generator,
    supporting the union definitions in Federer 4.1.22, p. 379. *)
Theorem polyhedral_simplex_generators_monotone
    (K L:smooth_compact_set hNX U):
  smooth_compact_carrier K `<=` smooth_compact_carrier L->
  polyhedral_simplex_generators K `<=` polyhedral_simplex_generators L.
Proof.
move=>hKL T [v [hHull hValue]];exists v;split;last exact:hValue.
exact:subset_trans hHull hKL.
Qed.

(** Source for [polyhedral_simplex_generators_empty]: the
    original empty compact index has no simplex generators,
    supporting Federer 4.1.22, p. 379. Even a zero-dimensional
    simplex has one vertex, so no empty-index exception is added. *)
Theorem polyhedral_simplex_generators_empty:
  forall T,~polyhedral_simplex_generators (@smooth_compact_empty R X NX hNX U) T.
Proof.
move=>T [v [hHull hValue]].
have hVertex:polyhedral_simplex_vertex_hull v (v ord0).
  apply:convex_hull_includes;exists ord0;by [].
exact:hHull (v ord0) hVertex.
Qed.

(** Source for [open_oriented_simplex_above_dimension]: the
    existing ambient-dimension vanishing of 4.1.10--4.1.11
    also holds for the generators used in 4.1.22, p. 379.
    It does not alter their original hull admissibility condition. *)
Theorem open_oriented_simplex_above_dimension (v:'I_(m.+1)->X):
  (n<m)%N->open_oriented_simplex_current v=0.
Proof.
move=>hDegree.
by rewrite /open_oriented_simplex_current
  (@oriented_simplex_current_above_dimension R h2 n m v hDegree) linear0.
Qed.
End PolyhedralCurrentGenerators.

(** Source for [open_oriented_simplex_point]: the actual
    zero-simplex used in Federer 4.1.22, p. 379, is
    the original point current of 4.1.11, p. 365, on
    U. This is agreement of the existing operations, including
    points outside U where the restriction is zero. *)
Theorem open_oriented_simplex_point (R:realType) (h2:(1+1:R)!=0) n
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (v:'I_1->R_n R n):
  @open_oriented_simplex_current R h2 n 0%N U hU v=
    @dirac_current R h2 n U hU (v ord0).
Proof.
rewrite /open_oriented_simplex_current oriented_simplex_current_point
  dirac_current_full_agreement.
by [].
Qed.
