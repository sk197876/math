(** Federer (1969), 4.1.27, p. 384:
    the consecutive-edge vector zeta has the
    same orientation as the earlier edge
    vector based at u_0. Subtract each
    preceding edge by the triangular exterior
    identity of 1.7.5, p. 32.
    No independence is needed for the equality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading FiniteExteriorPowers FinitePrefixes FiniteSpans FiniteSpanSpace
  TriangularProductChange FiniteIndependence IndependentProducts ExteriorHadamardBound
  CurrentSimplexFrame SimplexCubeParametrisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [simplex_consecutive_orientation_standard]: the consecutive
    edges in zeta have exactly the
    original ordered simplex orientation in 4.1.27,
    p. 384. This follows from the
    earlier triangular exterior-product law and includes
    every degenerate family and m=0. *)
Theorem simplex_consecutive_orientation_standard (R:realType) n m
    (v:'I_(m.+1)->R_n R n):
  simplex_consecutive_orientation v=
    e_lambda (current_simplex_edge_family v) (ord_tuple m).
Proof.
case:m v=>[|m] v.
- have hFamilies:simplex_consecutive_edge_family v=current_simplex_edge_family v.
    apply:funext=>i;by case:i.
  by rewrite /simplex_consecutive_orientation hFamilies.
- symmetry;apply:triangular_exterior_product_change=>i.
  have hResidual:current_simplex_edge_family v i-simplex_consecutive_edge_family v i=
      v (widen_ord (leqnSn m.+1) i)-v ord0.
    rewrite /current_simplex_edge_family /simplex_consecutive_edge_family.
    by rewrite opprB addrC addrA subrK.
  rewrite hResidual.
  case:(unliftP ord0 i)=>[j ->|->].
  + have hBelow:(val j<val (lift ord0 j))%N by exact:ltnSn.
    pose a:'I_(val (lift ord0 j)):=Ordinal hBelow.
    have hValue:family_prefix (ltnW (ltn_ord (lift ord0 j)))
        (current_simplex_edge_family v) a=
        v (widen_ord (leqnSn m.+1) (lift ord0 j))-v ord0.
      rewrite /family_prefix /current_simplex_edge_family.
      congr (v _-v ord0);apply:val_inj;by rewrite ?lift0.
    rewrite -hValue;exact:finite_span_generator.
  + rewrite [X in v X-_](_:_=ord0) ?subrr;[exact:in_finite_span_zero|exact:val_inj].
Qed.

(** Source for [simplex_consecutive_orientation_nonzero]: under the
    original affine-independence condition in 4.1.27,
    p. 384, zeta is nonzero by
    the existing independent-product theorem of 1.6.1.
    The nonzero empty product includes m=0. *)
Theorem simplex_consecutive_orientation_nonzero (R:realType) (h2:(1+1:R)!=0) n m
    (v:'I_(m.+1)->R_n R n):
  is_nondegenerate_current_simplex v->simplex_consecutive_orientation v!=0.
Proof.
move=>hIndependent;rewrite simplex_consecutive_orientation_standard.
exact:(@independent_product_nonzero R h2 (R_n R n) m
  (current_simplex_edge_family v) hIndependent).
Qed.

(** Source for [simplex_consecutive_orientation_degenerate_zero]: dependent
    original vertices give zeta=0 in
    the wedge formula of 4.1.27,
    p. 384. The normalized nondegenerate density
    is kept separate from this zero-current case. *)
Theorem simplex_consecutive_orientation_degenerate_zero (R:realType) n m
    (v:'I_(m.+1)->R_n R n):
  ~is_nondegenerate_current_simplex v->simplex_consecutive_orientation v=0.
Proof.
move=>hDependent;apply:contrapT=>hNonzero;apply:hDependent.
have hBoolean:simplex_consecutive_orientation v!=0 by apply/eqP;exact:hNonzero.
rewrite simplex_consecutive_orientation_standard in hBoolean.
exact:exterior_product_nonzero_independent hBoolean.
Qed.
