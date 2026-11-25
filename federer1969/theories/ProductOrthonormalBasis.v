(** Federer (1969), 1.7.11, p. 36: the factor inclusions
    give an orthonormal basis of the product before the common
    directions are rotated into diagonal and antidiagonal pairs.
    Source context: ProductInnerUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP ProductInner ProductLinearMaps ProductFiniteBasis
  OrthonormalFamilies OrthonormalConcatenation Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [cartesian_basis_orthonormal]: Federer 1.7.11,
    p. 36, supporting orthonormal product basis: the inclusions
    of orthonormal families from separate factors are perpendicular. *)
Theorem cartesian_basis_orthonormal (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n m (e : 'I_n -> V) (f : 'I_m -> W)
    (he : orthonormal_family B e) (hf : orthonormal_family C f) :
  orthonormal_family (product_inner hB hC) (cartesian_basis e f).
Proof.
apply: (@orthonormal_concatenation R _ _ (product_inner_productP hB hC)).
- move=> i j; by rewrite product_innerE /product_left /=
    (bil0l (inner_bilinear hC)) addr0 he.
- move=> i j; by rewrite product_innerE /product_right /=
    (bil0l (inner_bilinear hB)) add0r hf.
- move=> i j; by rewrite product_innerE /product_left /product_right /=
    (bil0r (inner_bilinear hB)) (bil0l (inner_bilinear hC)) add0r.
Qed.
