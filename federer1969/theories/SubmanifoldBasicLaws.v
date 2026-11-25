(** Federer (1969), 3.1.19, p. 231: dimension and the isolated-point
    implication for zero-dimensional submanifolds, using only the
    abstract straightening charts and inverse laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  FiniteCoordinates LinearBasis FiniteDualDimension Annihilator FiniteDimension
  FiniteIndependence FiniteBasisComparison NormDifferentialUP NormDiffeomorphismUP
  EuclideanSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_isolated_point]: a point isolated relative to S,
    as used in the last sentence of Federer 3.1.19, p. 231. An ambient
    neighbourhood meets S only at the point itself. *)
Definition norm_isolated_point (R:realType) (X:lmodType R) (NX:X->R)
    (S:set X) (a:X) := S a /\ norm_domain_interior NX (fun x=>S x -> x=a) a.

(** Source for [grassmann_zero_space]: supporting the zero-dimensional
    plane in the last sentence of Federer 3.1.19, p. 231. The basis
    definition of dimension in 1.6.2 forces this plane to be {0}. *)
Lemma grassmann_zero_space (K:fieldType) (X:lmodType K) (Z:G X 0) x :
  grassmann_val Z x <-> x=0.
Proof.
split.
- move=>hx; have [e he]:=grassmann_proof Z.
  have hh:=congr1 subspace_val (basis_vector_expansion he (subspace_lift hx)).
  by rewrite big_ord0 linear0 in hh.
- move=>->; exact: subspace_zero.
Qed.

(** Source for [empty_euclidean_submanifold]: the empty-set boundary
    of the definition in Federer 3.1.19, p. 231. No global bound mu<=n
    may be imposed when there are no points at which to choose a chart. *)
Lemma empty_euclidean_submanifold (R:realType) n mu k :
  @is_euclidean_submanifold R n mu k set0.
Proof. by move=>b hb; case:hb. Qed.

(** Source for [submanifold_dimension_at_point]: the local plane in
    condition (1), Federer 3.1.19, p. 231, has dimension at most n.
    This supporting bound is derived at a point, not added to the
    definition for possibly empty subsets. *)
Lemma submanifold_dimension_at_point (R:realType) n mu k (B:set (R_n R n)) b :
  @is_euclidean_submanifold R n mu k B -> B b -> (mu<=n)%N.
Proof.
move=>hB hb.
have [T [C [sigma [tau [Z hZ]]]]]:=@hB b hb.
have [e he]:=grassmann_proof Z.
have hi:=@finite_independent_map R (Finite.clone 'I_mu _)
  (subspace_space (grassmann_val Z)) (R_n R n)
  (subspace_inclusion (grassmann_val Z)) e
  (@subspace_val_injective R (R_n R n) (grassmann_val Z)) (finite_basis_independent he).
have hd:=@finite_independent_dimension R (finite_basis_vect (@coordinate_basisP R n))
  mu (fun i=>subspace_val (e i)) hi.
by rewrite finite_basis_dimension card_ord in hd.
Qed.

(** Source for [zero_submanifold_point_isolated]: the forward half
    of the final assertion in Federer 3.1.19, p. 231: every point of
    a zero-dimensional submanifold is isolated. Every class k>=0 and
    every ambient dimension are included. *)
Theorem zero_submanifold_point_isolated (R:realType) n k (B:set (R_n R n)) b :
  @is_euclidean_submanifold R n 0 k B -> B b ->
  norm_isolated_point (inner_norm (@euclidean_inner_productP R n)) B b.
Proof.
move=>hB hb; split=>//.
have [T [C [sigma [tau [Z hZ]]]]]:=@hB b hb.
have hT:=@submanifold_straightening_neighbourhood R n 0 k B b T C sigma tau Z hZ.
have hD:=@submanifold_straightening_diffeomorphism R n 0 k B b T C sigma tau Z hZ.
have hIm:=@submanifold_straightening_image R n 0 k B b T C sigma tau Z hZ.
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hbT:=@norm_domain_interior_member R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) hNX T b hT.
have hzero x (hx:B x /\ T x):sigma x=0.
  have hi:(sigma @` (B `&` T)) (sigma x) by exists x.
  rewrite hIm in hi; exact: (grassmann_zero_space Z (sigma x)).1 hi.1.
have hzb:=hzero b (conj hb hbT).
have [r [hr hball]]:=hT.
exists r; split=>// h hh hBh.
have hhT:=hball h hh.
have hz:=hzero (b+h) (conj hBh hhT).
have hinvh:=@norm_diffeomorphism_left_inverse R (R_n R n) (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R n))
  hNX hNX T C sigma tau k hD (b+h) hhT.
have hinvb:=@norm_diffeomorphism_left_inverse R (R_n R n) (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R n))
  hNX hNX T C sigma tau k hD b hbT.
rewrite hz in hinvh; rewrite hzb in hinvb.
exact (eq_trans (esym hinvh) hinvb).
Qed.
