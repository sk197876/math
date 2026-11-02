(** Federer (1969), 1.7.5, p. 32: corrected equality criterion for the
    product-norm bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerCauchy
  InnerExterior InnerExteriorPositivity InnerExteriorTriangular ExteriorNorm
  ExteriorHadamardBound ExteriorProductFactors FiniteProductEquality
  GramSchmidt OrthonormalFamilies OrthonormalisationUP
  ExteriorGrading FiniteExteriorPowers ExteriorExpansion Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Equality.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable m : nat.
Variable u : 'I_m -> V.

(** Source for [orthogonal_product_norm]: Federer 1.7.5,
    p. 32, mutually orthogonal factors attain equality in the
    product-norm bound, including zero factors and the empty family. *)
Theorem orthogonal_product_norm :
  (forall i j, i != j -> B (u i) (u j) = 0) ->
  exterior_norm h2 hB (e_lambda u (ord_tuple m)) = \prod_i inner_norm hB (u i).
Proof.
move=> ho; apply: inner_norm_value.
- apply: prodr_ge0 => i _; exact: inner_norm_nonnegative.
- have ht (i j : 'I_m) : (j < i)%N -> B (u j) (u i) = 0.
    move=> hj; apply: ho; apply/eqP=> he; by rewrite he ltnn in hj.
  rewrite (@exterior_inner_triangular R h2 V B hB m u u ht) foldrE big_map /=.
  rewrite -product_index_enum -prodrXl; apply: eq_bigr => i _; exact: inner_norm_sqr.
Qed.

(** Source for [exterior_product_norm_equality_nonzero]:
    Federer 1.7.5, p. 32, the printed equality condition is
    valid when every factor is nonzero. Gram-Schmidt reduces
    equality to equality in each individual Cauchy bound. *)
Theorem exterior_product_norm_equality_nonzero :
  (forall i, u i != 0) ->
  exterior_norm h2 hB (e_lambda u (ord_tuple m)) = (\prod_i inner_norm hB (u i)) ->
  forall i j, i != j -> B (u i) (u j) = 0.
Proof.
move=> hn heq.
have hp : 0 < \prod_i inner_norm hB (u i).
  apply: prodr_gt0 => i _; by rewrite inner_norm_gt0 hn.
have hx : e_lambda u (ord_tuple m) != 0.
  apply/eqP=> hz; by rewrite -heq hz exterior_norm_zero ltxx in hp.
have hu := exterior_product_nonzero_independent hx.
have [v hv] := @gram_schmidt_exists R V B hB m u hu.
have ho := orthonormalisation_orthonormal hv.
have hb i : 0 <= `|B (u i) (v i)| <= inner_norm hB (u i).
  apply/andP; split; first exact: normr_ge0.
  exact (@gram_schmidt_diagonal_bound R V B hB m u v ho i).
have hh := @nonnegative_product_equality R (Finite.clone 'I_m _)
  (fun i => `|B (u i) (v i)|) (fun i => inner_norm hB (u i)) hb.
have hnz : (\prod_i inner_norm hB (u i)) != 0 := lt0r_neq0 hp.
rewrite -(gram_schmidt_exterior_norm_product h2 hB hu hv) heq eqxx (negbTE hnz) orFb in hh.
have hdiag i : `|B (u i) (v i)| = inner_norm hB (u i).
  apply/eqP; exact: (forallP (esym hh)) i.
have hscale i : u i = B (u i) (v i) *: v i.
  have hvn : v i != 0.
    by rewrite -(inner_positive hB) ho eqxx ltr01.
  have hs : B (u i) (v i)^+2 = B (u i) (u i) * B (v i) (v i).
    rewrite ho eqxx mulr1 -(inner_norm_sqr hB) -(hdiag i).
    by rewrite -normrX ger0_norm ?sqr_ge0.
  have h := (proj1 (inner_cauchy_equality hB (u i) hvn)) hs.
  by rewrite ho eqxx divr1 in h.
move=> i j hij; rewrite (hscale i) (hscale j)
  (bilZl (inner_bilinear hB)) (bilZr (inner_bilinear hB)) ho (negbTE hij).
change (B (u i) (v i) * (B (u j) (v j) * 0) = 0).
by rewrite !mulr0.
Qed.

(** Source for [exterior_product_norm_equality]: Federer 1.7.5, p. 32,
    corrected iff: equality holds exactly when at least one factor is zero
    or the factors are mutually orthogonal. *)
Theorem exterior_product_norm_equality :
  exterior_norm h2 hB (e_lambda u (ord_tuple m)) = (\prod_i inner_norm hB (u i)) <->
  (exists i, u i = 0) \/ (forall i j, i != j -> B (u i) (u j) = 0).
Proof.
split.
- move=> he; case: (pselect (exists i, u i = 0)) => [hz|hz]; first by left.
  right; apply: exterior_product_norm_equality_nonzero he => i.
  apply/eqP=> hi; apply: hz; by exists i.
- move=> [[i hi]|ho]; last exact: orthogonal_product_norm.
  have hz : e_lambda u (ord_tuple m) = 0.
    apply: (@exterior_product_zero_entry R (Choice.clone 'I_m _) V u m (ord_tuple m) i) hi.
    exact: mem_enum.
  rewrite hz exterior_norm_zero; symmetry; apply/eqP/prodf_eq0.
  exists i => //; by rewrite hi inner_norm0 eqxx.
Qed.
End Equality.
