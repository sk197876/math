(** Federer (1969), 4.1.11, p. 366: every ordered
    m-simplex is an affine image of any nondegenerate
    m-simplex in R^m. Reuse basis interpolation of
    1.7.3, p. 30, the dimension theorem of 1.6.1,
    pp. 23–24, and the opaque affine space of 2.7.16,
    pp. 133–134. Target vertices may be dependent. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom LinearBasis FiniteIndependence FiniteBasisComparison FiniteBasisCriterion
  FiniteDimension FiniteCoordinates GrassmannAbbreviations Biorthogonal BasisInterpolation
  AffineMaps AffineMapSpaceUP AffineMapSpaceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_simplex_edge_family]: the original
    edge family u_1-u_0,...,u_m-u_0 used to interpret
    nondegeneracy in Federer 4.1.11, p. 366; compare
    the simplex computation of 2.7.16, p. 136. *)
Definition current_simplex_edge_family (R:realType) n m
    (v:'I_(m.+1)->R_n R n):'I_m->R_n R n:=fun i=>v (lift ord0 i)-v ord0.

(** Source for [is_nondegenerate_current_simplex]: the
    original nondegenerate simplex has independent edges,
    supporting the affine parametrisation in Federer
    4.1.11, p. 366. This is a predicate, not a chosen
    coordinate construction or an extra target hypothesis. *)
Definition is_nondegenerate_current_simplex (R:realType) n m
    (v:'I_(m.+1)->R_n R n):Prop:=finite_independent (current_simplex_edge_family v).

(** Source for [current_standard_simplex_vertices]: the
    existing origin and standard basis, supporting the
    source reduction in Federer 4.1.11, p. 366, as
    already used for the simplex of 2.7.16, p. 136. *)
Definition current_standard_simplex_vertices (R:realType) m:'I_(m.+1)->R_n R m:=
  ordinal_cons 0 (@coordinate_basis R m).

(** Source for [current_standard_simplex_edges]: its
    original edges are the standard basis, supporting
    Federer 4.1.11, p. 366. The empty edge family
    in dimension zero is included. *)
Lemma current_standard_simplex_edges (R:realType) m:
  current_simplex_edge_family (@current_standard_simplex_vertices R m)=@coordinate_basis R m.
Proof.
apply:funext=>i;by rewrite /current_simplex_edge_family /current_standard_simplex_vertices
  ordinal_consS ordinal_cons0 subr0.
Qed.

(** Source for [current_standard_simplex_nondegenerate]:
    the standard source simplex is nondegenerate,
    supporting the dimension reduction in Federer
    4.1.11, p. 366, including dimension zero. *)
Lemma current_standard_simplex_nondegenerate (R:realType) m:
  is_nondegenerate_current_simplex (@current_standard_simplex_vertices R m).
Proof.
rewrite /is_nondegenerate_current_simplex current_standard_simplex_edges.
exact:(finite_basis_independent (@coordinate_basisP R m)).
Qed.

(** Source for [current_simplex_nondegenerate_basis]: the
    edges of an original nondegenerate m-simplex in R^m
    form a basis, supporting Federer 4.1.11, p. 366,
    by the preceding finite-dimensional basis theorem. *)
Lemma current_simplex_nondegenerate_basis (R:realType) m (v:'I_(m.+1)->R_n R m):
  is_nondegenerate_current_simplex v->is_basis (current_simplex_edge_family v).
Proof.
move=>hV.
apply:(@finite_independent_basis R (finite_basis_vect (@coordinate_basisP R m)) m
  (current_simplex_edge_family v));last exact:hV.
by rewrite finite_basis_dimension card_ord.
Qed.

(** Source for [current_simplex_affine_vertices_exists]:
    an affine map sends the ordered vertices of any given
    nondegenerate m-simplex in R^m to every prescribed
    ordered m+1 vertices in R^n, supporting Federer
    4.1.11, p. 366. The target may be degenerate. *)
Theorem current_simplex_affine_vertices_exists (R:realType) m n
    (w:'I_(m.+1)->R_n R m) (v:'I_(m.+1)->R_n R n):
  is_nondegenerate_current_simplex w->
  exists A:R_n R m->R_n R n,is_affine_map A /\forall k,A (w k)=v k.
Proof.
move=>hW.
pose X:=R_n R m;pose Y:=R_n R n.
pose hBasis:=current_simplex_nondegenerate_basis hW.
pose L:=hom_of_linear (basis_interpolation hBasis (current_simplex_edge_family v)).
pose member:=@affine_space_iso_inv R X Y (affine_maps X Y) (@affine_map_eval R X Y)
  (@affine_mapsP R X Y) (L,v ord0-L (w ord0)).
pose A:=@affine_map_eval R X Y member.
have hAffine:is_affine_map A:=affine_space_eval_affine (@affine_mapsP R X Y) member.
have hValues x:A x=v ord0+L (x-w ord0).
  rewrite /A /member affine_space_iso_invE.
  change ((v ord0-L (w ord0))+L x=v ord0+L (x-w ord0)).
  by rewrite (linearB (hom_as_linear L)) addrA addrAC.
exists A;split;first exact:hAffine.
move=>k;case:(unliftP ord0 k)=>[i ->|->].
- rewrite hValues.
  have hEdge:L (w (lift ord0 i)-w ord0)=v (lift ord0 i)-v ord0.
    exact:(@basis_interpolationE R (Choice.clone 'I_m _) X Y
      (current_simplex_edge_family w) hBasis (current_simplex_edge_family v) i).
  by rewrite hEdge addrC subrK.
- by rewrite hValues subrr linear0 addr0.
Qed.
