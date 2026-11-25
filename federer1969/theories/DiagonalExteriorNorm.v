(** Federer (1969), 1.7.11, p. 36: the factor 2^(lambda/2). This supporting
    proof uses the diagonal map of 1.6.5, p. 25, and orthogonality of its
    normalisation by 1/sqrt(2). It is the same metric scaling as the
    displayed antidiagonal basis in the book. Source context and limits:
    ProductInnerUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP ProductInner ProductSpaceMaps
  ProductDiagonalNormalization OrthogonalMaps Bilinear ExteriorNorm
  ExteriorNormNaturality ExteriorMapScaling ExteriorMaps ExteriorGrading.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Diagonal.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation W := (GRing.Lmodule.clone R (V * V)%type _).

(** Source for [normalised_diagonal]: Federer 1.7.11,
    p. 36, supporting map x maps to (x,x)/sqrt(2), the
    normalised diagonal used in the product-space calculation. *)
Definition normalised_diagonal (x : V) : W :=
  (Num.sqrt (2 : R))^-1 *: FedererProduct.g_map V x.

(** Source for [normalised_diagonal_linear]: Federer 1.7.11,
    p. 36, linearity of the normalised diagonal map. *)
Lemma normalised_diagonal_linear : linear normalised_diagonal.
Proof. by move=> c x y; rewrite /normalised_diagonal linearP scalerDr !scalerA mulrC. Qed.
HB.instance Definition _ := GRing.isLinear.Build R V W *:%R
  normalised_diagonal normalised_diagonal_linear.

(** Source for [normalised_diagonal_orthogonal]: Federer
    1.7.11, p. 36, supporting metric computation: dividing
    (x,x) by sqrt(2) gives an orthogonal inclusion. *)
Lemma normalised_diagonal_orthogonal :
  is_orthogonal_map B (product_inner hB hB) normalised_diagonal.
Proof.
move=> x y.
rewrite /normalised_diagonal
  (bilZl (inner_bilinear (product_inner_productP hB hB)))
  (bilZr (inner_bilinear (product_inner_productP hB hB)))
  product_innerE /=.
change ((Num.sqrt (2 : R))^-1 * ((Num.sqrt (2 : R))^-1 * (B x y + B x y)) = B x y).
rewrite mulrA -expr2 -mulr2n.
change (((Num.sqrt (2 : R))^-1)^+2 * (B x y *+ 2) = B x y).
rewrite -(mulr_natl (B x y) 2) mulrA inverse_sqrt_two_square mul1r.
by [].
Qed.

(** Source for [diagonal_exterior_norm]: Federer 1.7.11,
    p. 36, supporting scaling identity: the degree-lambda
    diagonal map multiplies every exterior norm by sqrt(2)^lambda.
    The empty exterior power has scale one. *)
Theorem diagonal_exterior_norm m (x : exterior_power V m) :
  exterior_norm h2 (product_inner_productP hB hB)
    (exterior_power_map (FedererProduct.g_map V) m x) =
    (Num.sqrt (2 : R))^+m * exterior_norm h2 hB x.
Proof.
pose d : {linear V -> W} := GRing.Linear.clone _ _ _ _ normalised_diagonal _.
have hd v : FedererProduct.g_map V v = Num.sqrt (2 : R) *: d v.
  rewrite /d /normalised_diagonal scalerA mulfV ?scale1r //.
  apply: lt0r_neq0; by rewrite sqrtr_gt0 ltr0n.
rewrite (@exterior_power_map_scale R V W d (FedererProduct.g_map V)
  (Num.sqrt (2 : R)) hd) exterior_norm_scale normrX
  (ger0_norm (sqrtr_ge0 _)).
congr (_ * _).
exact (@exterior_norm_orthogonal_natural R h2 V W B
  (product_inner hB hB) hB (product_inner_productP hB hB)
  d normalised_diagonal_orthogonal m x).
Qed.
End Diagonal.
