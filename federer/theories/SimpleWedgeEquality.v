(** Federer (1969), 1.7.5, p. 32: equality in the wedge norm bound for two
    nonzero simple multivectors. Orthogonality is stated directly for the
    associated subspaces. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP ExteriorNorm SimpleOrthonormalFactor
  OrthonormalFamilies OrthonormalWedgeEquality ProductAssociatedOrthogonality
  AssociatedSubspace SimpleElementary ExteriorGrading FiniteExteriorPowers
  ExteriorHomogeneousProducts Bilinear ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [simple_wedge_norm_equality]: Federer 1.7.5,
    p. 32, if xi and eta are simple and nonzero, equality
    in |xi wedge eta| <= |xi| |eta| holds exactly when their
    associated vector subspaces are orthogonal. *)
Theorem simple_wedge_norm_equality (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    p q (x : exterior_power V p) (y : exterior_power V q)
    (hx : x != 0) (hy : y != 0) (sx : simple x) (sy : simple y) :
  exterior_norm h2 hB (exterior_product x y) =
    exterior_norm h2 hB x * exterior_norm h2 hB y <->
  forall u v, FedererSimple.T x u -> FedererSimple.T y v -> B u v = 0.
Proof.
have [e [a [he [ha hxe]]]] := @simple_orthonormal_factor R h2 V B hB p x hx sx.
have [f [b [hf [hb hyf]]]] := @simple_orthonormal_factor R h2 V B hB q y hy sy.
have hen : e_lambda e (ord_tuple p) != 0.
  apply/eqP=> hz; by rewrite hxe hz scaler0 eqxx in hx.
have hfn : e_lambda f (ord_tuple q) != 0.
  apply/eqP=> hz; by rewrite hyf hz scaler0 eqxx in hy.
have hn : `|a| * `|b| != 0 by rewrite mulf_eq0 !normr_eq0 negb_or ha hb.
have hmetric : exterior_norm h2 hB (exterior_product x y) =
    exterior_norm h2 hB x * exterior_norm h2 hB y <->
    exterior_norm h2 hB (exterior_product (e_lambda e (ord_tuple p))
      (e_lambda f (ord_tuple q))) = 1.
  rewrite hxe hyf (bilZl (@exterior_product_bilinear R V p q))
    (bilZr (@exterior_product_bilinear R V p q)) !exterior_norm_scale
    (orthonormal_product_unit_norm h2 hB he) (orthonormal_product_unit_norm h2 hB hf)
    !mulr1 mulrA.
  split; last by move=> ->; rewrite mulr1.
  move=> hh; apply: (mulfI hn); by rewrite mulr1.
have hspaces : (forall u v, FedererSimple.T x u -> FedererSimple.T y v -> B u v = 0) <->
    forall i j, B (e i) (f j) = 0.
  rewrite hxe hyf.
  have hh := @product_associated_orthogonality R h2 V B hB p q e f hen hfn.
  split.
  - move=> ho; apply: (proj1 hh) => u v hu hv; apply: ho.
    + exact: (proj2 (@associated_scale_nonzero R V p (e_lambda e (ord_tuple p)) a ha u)) hu.
    + exact: (proj2 (@associated_scale_nonzero R V q (e_lambda f (ord_tuple q)) b hb v)) hv.
  - move=> ho u v hu hv; apply: (proj2 hh ho).
    + exact: (proj1 (@associated_scale_nonzero R V p (e_lambda e (ord_tuple p)) a ha u)) hu.
    + exact: (proj1 (@associated_scale_nonzero R V q (e_lambda f (ord_tuple q)) b hb v)) hv.
exact (iff_trans hmetric (iff_trans
  (@orthonormal_products_wedge_equality R h2 V B hB p q e f he hf) (iff_sym hspaces))).
Qed.
