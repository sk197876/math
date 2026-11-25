(** Federer (1969), 1.7.11, p. 36: regarding each simple unit multivector as
    a unit top vector of its associated space. This uses the first corollary
    of 1.6.1, p. 24. The direction used here includes degree zero under the
    literal empty-product convention. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductRestriction
  ExteriorNorm ExteriorNormNaturality ExteriorMaps ExteriorGrading
  FiniteExteriorPowers SimpleDimensionCriterion SimpleElementary
  AssociatedSubspace SubspaceCarrier LinearBasis CovectorProductNaturality OrthogonalMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [simple_unit_associated_lift]: Federer 1.7.11,
    p. 36, supporting intrinsic unit volume of T(xi). A simple
    unit k-vector lifts to a unit top vector of its k-dimensional
    associated space, and the subspace inclusion sends it back to xi. *)
Theorem simple_unit_associated_lift (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    k (x : exterior_power V k) (hs : simple x) (hx : exterior_norm h2 hB x = 1) :
  exists e : 'I_k -> subspace_space (FedererSimple.T x),
    is_basis e /\
    exterior_norm h2 (restricted_inner_productP hB (FedererSimple.T x))
      (e_lambda e (ord_tuple k)) = 1 /\
    exterior_power_map (GRing.Linear.clone _ _ _ _
      (@subspace_val R V (FedererSimple.T x)) _) k (e_lambda e (ord_tuple k)) = x.
Proof.
have hn : x != 0.
  apply/eqP=> hz; move: hx; rewrite hz exterior_norm_zero => /eqP.
  by rewrite eq_sym oner_eq0.
have [e [he hex]] := @simple_is_basis_product R h2 V k x hn hs.
exists e; split=> //.
have hi : exterior_power_map (GRing.Linear.clone _ _ _ _
    (@subspace_val R V (FedererSimple.T x)) _) k (e_lambda e (ord_tuple k)) = x.
  by rewrite exterior_basis_product_natural -hex.
split=> //.
have ho : OrthogonalMaps.is_orthogonal_map
    (@restricted_inner_product R V B (FedererSimple.T x)) B
    (GRing.Linear.clone _ _ _ _ (@subspace_val R V (FedererSimple.T x)) _)
    by move=> u v; reflexivity.
have hh := @exterior_norm_orthogonal_natural R h2
  (GRing.Lmodule.clone R (subspace_space (FedererSimple.T x)) _) V
  (@restricted_inner_product R V B (FedererSimple.T x)) B
  (restricted_inner_productP hB (FedererSimple.T x)) hB
  (GRing.Linear.clone _ _ _ _ (@subspace_val R V (FedererSimple.T x)) _) ho k
  (e_lambda e (ord_tuple k)).
rewrite hi hx in hh; exact: esym hh.
Qed.
