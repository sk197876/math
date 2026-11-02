(** Federer (1969), 1.7.11, p. 36: the wedge of two Hodge duals is
    independent of the choice of unit orientation. Supporting consequence of
    1.7.8, p. 34: reversing orientation negates each Hodge map, so the two
    signs cancel in their product. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP ExteriorNorm ExteriorGrading
  ExteriorHomogeneousProducts FiniteExteriorPowers LinearBasis OrthonormalFamilies
  UnitTopVolume HodgeMaps Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [hodge_product_basis_volume]: Federer 1.7.11,
    p. 36, supporting orientation independence of the wedge
    of the two starred inputs. Both stars use the same unit volume;
    this is essential for the two orientation factors to cancel. *)
Theorem hodge_product_basis_volume (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (ho : orthonormal_family B e)
    (E : exterior_power V n) (hE : exterior_norm h2 hB E = 1)
    k l (hk : (k <= n)%N) (hl : (l <= n)%N)
    (x : exterior_power V k) (y : exterior_power V l) :
  exterior_product (hodge_vector h2 hB E hk x) (hodge_vector h2 hB E hl y) =
  exterior_product
    (hodge_vector h2 hB (e_lambda e (ord_tuple n)) hk x)
    (hodge_vector h2 hB (e_lambda e (ord_tuple n)) hl y).
Proof.
have [c [hc hc2]] := @unit_top_volume_scalar R h2 V B hB n e he ho E hE.
by rewrite hc !hodge_vector_volume_scale
  (bilZl (@exterior_product_bilinear R V (n-k) (n-l)))
  (bilZr (@exterior_product_bilinear R V (n-k) (n-l)))
  scalerA -expr2 hc2 scale1r.
Qed.

(** Source for [unit_exterior_degree_bound]: Federer 1.7.11,
    p. 36, supporting automatic bounds k,m<=n for the unit
    input vectors, by the vanishing above dimension in 1.3.2,
    pp. 14-15. Thus the domains of the two Hodge maps impose
    no additional mathematical hypothesis. *)
Lemma unit_exterior_degree_bound (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) k (x : exterior_power V k) :
  exterior_norm h2 hB x = 1 -> (k <= n)%N.
Proof.
move=> hx; case: (leqP k n) => // hn.
have hz := @exterior_power_above_dimension R n V e he h2 k hn x.
move: hx; rewrite hz exterior_norm_zero => /eqP.
by rewrite eq_sym oner_eq0.
Qed.
