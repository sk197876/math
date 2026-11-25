(** Federer (1969), 1.7.5, p. 32: the simple-factor exterior norm bound in
    finite dimension. An adapted orthonormal basis reduces the assertion to
    deleting coordinate squares. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior ExteriorNorm
  ExteriorBasisWedgeNorm SimpleOrthonormalBasis SimpleAdaptedBasis
  OrthonormalFamilies OrthonormalBilinearCoordinates FinitePrefixes
  LinearBasis FiniteExteriorPowers ExteriorGrading ExteriorIndices
  ExteriorHomogeneousProducts Bilinear SimpleElementary InitialIndices AssociatedSubspace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_basis_wedge_norm_bound]: Federer
    1.7.5, p. 32, multiplication on the right by a unit
    orthonormal basis product has norm at most one on every degree. *)
Theorem finite_basis_wedge_norm_bound (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (ho : orthonormal_family B e)
    p q (kappa : Lambda n q) (x : exterior_power V p) :
  exterior_norm h2 hB (exterior_product x (e_lambda e (val kappa))) <= exterior_norm h2 hB x.
Proof.
have hb := @finite_e_lambda_basis R n V e he h2 p.
rewrite (@orthonormal_basis_vector_expansion R (exterior_power V p)
  (Finite.clone (Lambda n p) _) (fun lambda => e_lambda e (val lambda)) hb x).
exact (@exterior_basis_wedge_norm_bound R h2 V B hB n e ho p q kappa _).
Qed.

(** Source for [finite_simple_right_wedge_norm_bound]: Federer
    1.7.5, p. 32, if the right factor is simple then the
    norm of the wedge is bounded by the product of the norms.
    Zero factors and degree zero are included. *)
Theorem finite_simple_right_wedge_norm_bound (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e)
    p q (x : exterior_power V p) (y : exterior_power V q) :
  simple y -> exterior_norm h2 hB (exterior_product x y) <=
    exterior_norm h2 hB x * exterior_norm h2 hB y.
Proof.
move=> hs; case: (eqVneq y 0) => [->|hy].
- by rewrite (bil0r (@exterior_product_bilinear R V p q)) !exterior_norm_zero mulr0 lexx.
have hq : (q <= n)%N.
  case: (leqP q n) => [hq|hn]; first by [].
  have hz := @exterior_power_above_dimension R n V e he h2 q hn y.
  by rewrite hz eqxx in hy.
have [d [c [hd [ho [hc ->]]]]] :=
  @simple_orthonormal_adapted_basis R h2 V B hB n e he q hq y hy hs.
rewrite (bilZr (@exterior_product_bilinear R V p q)) !exterior_norm_scale.
have hn : exterior_norm h2 hB (e_lambda d (val (Lambda_initial hq))) = 1.
  rewrite initial_productE; exact (@orthonormal_product_unit_norm R h2 V B hB q
    (family_prefix hq d) (@orthonormal_family_prefix R V B n d ho q hq)).
rewrite hn mulr1 (mulrC (exterior_norm h2 hB x) `|c|).
apply: ler_wpM2l; first exact: normr_ge0.
exact (@finite_basis_wedge_norm_bound R h2 V B hB n d hd ho p q (Lambda_initial hq) x).
Qed.
