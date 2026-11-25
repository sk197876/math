(** Federer (1969), 1.7.5, p. 32: the product-norm inequality, including
    zero and dependent factors. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities
  InnerExterior ExteriorNorm GramSchmidt GramSchmidtExteriorFactor
  OrthonormalFamilies OrthonormalisationUP FiniteIndependence
  SimpleWordIndependence ExteriorGrading ExteriorAlgebra FiniteExteriorPowers
  GradedComponents ExteriorExpansion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_product_nonzero_independent]:
    Federer 1.7.5, p. 32, supporting separation of the
    independent case of Gram-Schmidt from the vanishing product case.
    This is the existing 1.6.1 fact expressed for a homogeneous product. *)
Lemma exterior_product_nonzero_independent (R : fieldType) (V : lmodType R)
    m (u : 'I_m -> V) :
  e_lambda u (ord_tuple m) != 0 -> finite_independent u.
Proof.
move=> hx; apply: nonzero_word_independent; apply/eqP=> hz.
apply: (elimT negP hx); apply/eqP; apply: val_inj.
change (component_val (e_lambda u (ord_tuple m)) = component_val (0 : exterior_power V m)).
by rewrite e_lambdaE linear0.
Qed.

(** Source for [gram_schmidt_exterior_norm_product]: Federer
    1.7.5, p. 32, the product formula for the norm after
    Gram-Schmidt, written as a finite product of absolute diagonal entries. *)
Lemma gram_schmidt_exterior_norm_product (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    m (u v : 'I_m -> V) (hu : finite_independent u)
    (hv : is_orthonormalisation B u v) :
  exterior_norm h2 hB (e_lambda u (ord_tuple m)) = \prod_i `|B (u i) (v i)|.
Proof.
rewrite (@gram_schmidt_exterior_norm R h2 V B hB m u v hu hv) foldrE big_map /= normr_prod.
by rewrite product_index_enum.
Qed.

(** Source for [gram_schmidt_diagonal_bound]: Federer
    1.7.5, p. 32, Cauchy's inequality bounds each diagonal
    coefficient by the length of the corresponding original vector. *)
Lemma gram_schmidt_diagonal_bound (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    m (u v : 'I_m -> V) (hv : orthonormal_family B v) i :
  `|B (u i) (v i)| <= inner_norm hB (u i).
Proof.
have hn : inner_norm hB (v i) = 1.
  apply: inner_norm_value; first exact: ler01.
  by rewrite expr1n hv eqxx.
have hh := inner_cauchy hB (u i) (v i).
by rewrite hn mulr1 in hh.
Qed.

(** Source for [exterior_product_norm_bound]: Federer
    1.7.5, p. 32, the norm of v1 wedge ... wedge vm is
    at most the product of the individual norms. This includes
    m=0 and all zero or dependent families. *)
Theorem exterior_product_norm_bound (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    m (u : 'I_m -> V) :
  exterior_norm h2 hB (e_lambda u (ord_tuple m)) <= \prod_i inner_norm hB (u i).
Proof.
case: (eqVneq (e_lambda u (ord_tuple m)) 0) => [hz|hx].
- rewrite hz exterior_norm_zero; apply: prodr_ge0 => i _; exact: inner_norm_nonnegative.
- have hu := exterior_product_nonzero_independent hx.
  have [v hv] := @gram_schmidt_exists R V B hB m u hu.
  rewrite (@gram_schmidt_exterior_norm_product R h2 V B hB m u v hu hv).
  apply: ler_prod => i _; apply/andP; split; first exact: normr_ge0.
  exact (@gram_schmidt_diagonal_bound R V B hB m u v
    (orthonormalisation_orthonormal hv) i).
Qed.
