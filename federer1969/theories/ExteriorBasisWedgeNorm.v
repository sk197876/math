(** Federer (1969), 1.7.5, p. 32: multiplication by an orthonormal exterior
    basis vector cannot increase the norm. The coordinate calculation is
    valid for an orthonormal family, without requiring it to span the
    ambient space. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorBasis
  InnerExteriorIndexProducts ExteriorNorm OrthonormalFamilies
  OrthonormalBilinearCoordinates BilinearFiniteCoordinates
  ExteriorGrading ExteriorHomogeneousProducts FiniteExteriorPowers ExteriorIndices
  Bilinear LinearBasis FiniteDualDimension Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Norm.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : orthonormal_family B e.
Variables p q : nat.
Variable kappa : Lambda n q.
Variable c : Lambda n p -> R.
Local Notation X := (\sum_lambda c lambda *: e_lambda e (val lambda)).
Local Notation Z := (e_lambda e (val kappa)).

(** Source for [exterior_basis_wedge_expansion]: Federer
    1.7.5, p. 32, supporting distribution of a fixed right
    exterior factor over the coordinate expansion. *)
Lemma exterior_basis_wedge_expansion :
  exterior_product X Z =
    \sum_lambda c lambda *: exterior_product (e_lambda e (val lambda)) Z.
Proof.
rewrite (big_morph (fun x => exterior_product x Z)
  (fun x y => bilDl (@exterior_product_bilinear R V p q) x y Z)
  (bil0l (@exterior_product_bilinear R V p q) Z)).
apply: eq_bigr => lambda _; by rewrite (bilZl (@exterior_product_bilinear R V p q)).
Qed.

(** Source for [exterior_basis_wedge_norm_square]: Federer 1.7.5, p. 32, the
    square norm after multiplying by e_kappa is the sum of coordinate
    squares for indices disjoint from kappa. *)
Theorem exterior_basis_wedge_norm_square :
  exterior_norm h2 hB (exterior_product X Z)^+2 =
    \sum_(lambda : Lambda n p) if uniq (val lambda ++ val kappa) then (c lambda)^+2 else 0.
Proof.
rewrite exterior_basis_wedge_expansion exterior_norm_square
  (bilinear_finite_expansion (exterior_inner_form_bilinear h2 hB (p+q))).
apply: eq_bigr => lambda _; rewrite (bigD1 lambda) //=.
rewrite (exterior_orthonormal_products_shared h2 hB he) eqxx /=.
have hz : (\sum_(mu | mu != lambda) (c lambda * c mu) *
    exterior_inner_form h2 hB
      (exterior_product (e_lambda e (val lambda)) Z)
      (exterior_product (e_lambda e (val mu)) Z)) = 0.
  apply: big1 => mu hm; by rewrite (exterior_orthonormal_products_shared h2 hB he)
    (negbTE hm) mulr0.
rewrite hz addr0; case: (uniq (val lambda ++ val kappa)); by rewrite ?mulr0 ?mulr1 ?expr2.
Qed.

(** Source for [exterior_basis_expansion_norm_square]: Federer
    1.7.5, p. 32, the square norm of an orthonormal exterior
    coordinate expansion is the sum of its squared coefficients. *)
Lemma exterior_basis_expansion_norm_square :
  exterior_norm h2 hB X^+2 = \sum_lambda (c lambda)^+2.
Proof.
rewrite exterior_norm_square
  (@orthonormal_bilinear_expansion R (exterior_power V p)
    (@exterior_inner_form R h2 V B hB p) (exterior_inner_form_bilinear h2 hB p)
    (Finite.clone (Lambda n p) _) (fun lambda => e_lambda e (val lambda))
    (@exterior_orthonormal_family R h2 V B hB n e he p) c c).
apply: eq_bigr => lambda _; by rewrite expr2.
Qed.

(** Source for [exterior_basis_wedge_norm_bound]: Federer
    1.7.5, p. 32, the simple-factor wedge bound for a unit
    basis product; deleting nonnegative coordinate squares decreases
    the norm. The other factor can be any linear combination. *)
Theorem exterior_basis_wedge_norm_bound :
  exterior_norm h2 hB (exterior_product X Z) <= exterior_norm h2 hB X.
Proof.
rewrite -(ler_sqr (exterior_norm_nonnegative h2 hB _) (exterior_norm_nonnegative h2 hB _))
  exterior_basis_wedge_norm_square exterior_basis_expansion_norm_square.
apply: ler_sum => lambda _; case: (uniq (val lambda ++ val kappa));
  by rewrite ?lexx ?sqr_ge0.
Qed.
End Norm.
