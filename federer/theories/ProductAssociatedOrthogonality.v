(** Federer (1969), 1.7.5, p. 32: interpreting the equality criterion as
    orthogonality of associated subspaces. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerOrthogonality
  AssociatedSubspace SimpleProducts FiniteExteriorPowers ModuleQuotient ExteriorGrading.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [product_associated_orthogonality]: Federer
    1.7.5, p. 32, the associated spaces of two nonzero
    products are orthogonal exactly when all cross-products of
    their factors vanish. This includes empty factor families. *)
Theorem product_associated_orthogonality (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    p q (e : 'I_p -> V) (f : 'I_q -> V)
    (he : e_lambda e (ord_tuple p) != 0) (hf : e_lambda f (ord_tuple q) != 0) :
  (forall x y, FedererSimple.T (e_lambda e (ord_tuple p)) x ->
    FedererSimple.T (e_lambda f (ord_tuple q)) y -> B x y = 0) <->
  forall i j, B (e i) (f j) = 0.
Proof.
split.
- move=> ho i j; apply: ho; exact: product_associated_generator.
- move=> ho x y hx hy.
  have hxs := proj1 (@product_associated_space R h2 V p e he x) hx.
  have hys := proj1 (@product_associated_space R h2 V q f hf y) hy.
  apply: (@inner_orthogonal_span R V B hB q f x y) hys => j.
  rewrite (inner_symmetric hB).
  apply: (@inner_orthogonal_span R V B hB p e (f j) x) hxs => i.
  by rewrite (inner_symmetric hB) ho.
Qed.
