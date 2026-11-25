(** Earlier mathematical use: Federer (1969), 4.1.27, p. 384,
    the degenerate simplex case in the original cube-current
    identity. Reuse the prepared lower-dimensional support proof;
    the retained locators also describe its later use in 4.1.32. *)
(** Federer (1969), 4.1.32, pp. 392–393:
    dependent vertices give a simplex carried by
    a plane of dimension strictly below its degree.
    This preserves the printed condition on genuine
    m-dimensional simplexes in the deformation assertion;
    it does not strengthen it to all tuples.
    The same supporting degeneracy statement is used in
    4.1.27, p. 384. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier LinearBasis
  FiniteCoordinates FiniteSpans FiniteSpanSpace FiniteIndependence
  FiniteSubspaceBasisExistence SpanningDimension SpanningDimensionBound
  GrassmannSubspaces GrassmannAbbreviations Biorthogonal EuclideanInnerProduct
  AffineMaps AffineSubspaceSpace InnerConvex ConvexHull
  CurrentSimplexFrame PolyhedralCurrentGenerators.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [degenerate_simplex_plane_exists]: a
    degenerate m-simplex has its full vertex hull
    in a plane of dimension less than m,
    supporting the original projective deformation proof
    of 4.1.32, pp. 392–393. The degree-zero
    case has no degenerate tuple and requires no
    chosen source point or negative dimension. *)
Theorem degenerate_simplex_plane_exists (R:realType) n m
    (v:'I_(m.+1)->R_n R n):
  ~is_nondegenerate_current_simplex v->
  exists d (A:set (R_n R n)),(d<m)%N /\
    @is_affine_subspace_dim R (R_n R n) d A /\
    @polyhedral_simplex_vertex_hull R n m v `<=` A.
Proof.
move=>hDegenerate.
pose X:=R_n R n.
pose edge:=@current_simplex_edge_family R n m v.
pose W:=@finite_span_subspace R X m edge.
have[d [b [hb hdAmbient]]]:=@finite_subspace_basis_exists R X n
  (@coordinate_basis R n) (@coordinate_basisP R n) W.
pose edgeW:'I_m->subspace_space W:=
  fun i=>@subspace_lift R X W (edge i) (@finite_span_generator R X m edge i).
have hSpan:forall x:subspace_space W,in_finite_span edgeW x.
  move=>x;have[c hc]:=subspace_valP x;exists c;apply:val_inj.
  rewrite linear_sum;change (subspace_val x=\sum_i c i*:edge i).
  exact:hc.
have hd:(d<=m)%N:=@spanning_dimension_bound R (subspace_space W) d b hb
  m edgeW hSpan.
have hNotEqual:d!=m.
  apply/eqP=>hEqual;subst d;apply:hDegenerate.
  have hIndependentW:=@spanning_dimension_independent R (subspace_space W)
    m b hb edgeW hSpan.
  have hIndependent:=@finite_independent_map R [the finType of 'I_m]
    (subspace_space W) X (@subspace_inclusion R X W) edgeW
    (@subspace_val_injective R X W) hIndependentW.
  exact:hIndependent.
have hLess:(d<m)%N by rewrite ltn_neqAle hNotEqual hd.
pose GW:@G R X d:=@GrassmannSubspace R X d W (ex_intro _ b hb).
pose A:=@affine_coset R X d (v ord0) GW.
have hA:@is_affine_subspace_dim R X d A.
  exists (v ord0),GW;by [].
have hVertices:forall i,A (v i).
  move=>i;case:(unliftP ord0 i)=>[k ->|->].
  - exact:(@finite_span_generator R X m edge k).
  - exact:(@affine_coset_base R X d (v ord0) GW).
have hConvex:is_inner_convex A.
  move=>x y hx hy t ht0 ht1.
  apply:(@affine_coset_is_affine_subspace R X d (v ord0) GW x y
    (1-t) t hx hy).
  exact:subrK.
exists d,A;split;first exact:hLess.
split;first exact:hA.
apply:convex_hull_least=>// x [i <-];exact:hVertices.
Qed.
