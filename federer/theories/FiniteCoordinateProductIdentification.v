(** Federer (1969), 2.6.6, p. 120: the finite products mu_a of the
    infinite-product theorem are "the cartesian product mu_a of the Daniell
    integrals mu_j corresponding to j in a (constructed by the method of
    2.6.4)", and satisfy "mu_b(f o p^b_a) = mu_a(f) mu_{b-a}(1) = mu_a(f)
    for f in K(X_a)". This file states these facts for the sealed family
    [finite_coordinate_product] used by [infinite_daniell_product], by
    specialising the results proved for every family with the laws
    [is_finite_coordinate_product_family]. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP DaniellIntegralUP MonotoneDaniellIntegralUP
  MonotoneDaniellIntegralSum FiniteCoordinateProjection FiniteCoordinateMarginal FiniteCoordinateProductUP
  FiniteCoordinateProduct InfiniteProductMarginals SubtypeCompactHausdorff DaniellProductUP DaniellProduct
  FiniteCoordinateSplit FiniteCoordinateAdjoinProduct FiniteCoordinateRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

Section Identification.
Variables (R : realType) (I : choiceType) (Y : I -> topologicalType).
Variables (A : forall i, (Y i -> R) -> R).
Variables (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i))).
Variables (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (@A i))
  (hA1 : forall i, @A i (fun _=>1) = 1).
Local Notation X := (prod_topology Y).
Local Notation C := (@finite_coordinate_product R I Y A hh hc hA hA1).

(** Source for [hC]: the abstract laws of the finite products of
    Federer 2.6.6, p. 120. *)
Let hC : is_finite_coordinate_product_family A C :=
  @finite_coordinate_product_specification R I Y A hh hc hA hA1.

(** Source for [finite_product_marginal_daniell_integral]: mu_a is a
    Daniell integral on K(X_a), Federer 2.6.6, p. 120. *)
Lemma finite_product_marginal_daniell_integral (F : {fset I}) :
  is_daniell_integral (@compactly_supported_continuous_functions R (finite_coordinate_space Y F))
    (finite_coordinate_marginal C F).
Proof.
exact: monotone_daniell_integral_is_daniell (@infinite_product_marginal_daniell R I Y A hh hc hA hA1 F).1.
Qed.

(** Source for [finite_product_adjoin_daniell_product]: mu_{a cup {i}}
    corresponds under psi : X_{a cup {i}} -> X_a x X_i to a functional
    with the laws of the product of mu_a and mu_i in Federer 2.6.4,
    p. 119; Federer 2.6.6, p. 120. *)
Theorem finite_product_adjoin_daniell_product (F : {fset I}) (i : I) :
  i \notin F ->
  is_daniell_product (finite_coordinate_marginal C F) (@A i)
    (@finite_coordinate_adjoined_functional R I Y C F i).
Proof. exact: (@finite_coordinate_adjoin_daniell_product R I Y A hh hc hA C hC F i). Qed.

(** Source for [finite_product_adjoin_value]: mu_{a cup {i}}(k o psi)
    is the value at k of the product functional of mu_a and mu_i of
    Federer 2.6.4, p. 119, for k in K(X_a x X_i); Federer 2.6.6,
    p. 120, "constructed by the method of 2.6.4". *)
Theorem finite_product_adjoin_value (F : {fset I}) (i : I)
    (k : (finite_coordinate_space Y F * Y i)%type -> R) :
  i \notin F -> compactly_supported_continuous_functions k ->
  finite_coordinate_marginal C (i |` F) (k \o @finite_coordinate_split I Y F i)=
    daniell_product (@finite_coordinate_space_hausdorff I Y hh F)
      (compact_space_locally_compact (@finite_coordinate_space_compact I Y hc F))
      (@hh i) (compact_space_locally_compact (@hc i))
      (finite_product_marginal_daniell_integral F)
      (monotone_daniell_integral_is_daniell (@hA i)) k.
Proof.
move=> hi hk.
exact: (@finite_coordinate_adjoin_daniell_product_value R I Y A hh hc hA C hC F i _ _ _ _ _ _ k hi hk).
Qed.

(** Source for [finite_product_separated_value]: mu_a(prod_{j in a}
    f_j o pi_j) = prod_{j in a} mu_j(f_j), the values of the product
    integral of Federer 2.6.4, p. 119, on separated products, for the
    finite products of 2.6.6, p. 120; the left side is mu_a evaluated
    on L_a. *)
Theorem finite_product_separated_value (F : {fset I}) (f : forall j, Y j -> R) :
  (forall j, j \in F -> compactly_supported_continuous_functions (f j)) ->
  C F (fun x : X=>\prod_(j <- F) f j (x j))=\prod_(j <- F) @A j (f j).
Proof. exact: (@finite_coordinate_product_separated_value R I Y A hc hA C hC F f). Qed.

(** Source for [finite_product_marginal_restriction]: the displayed
    chain mu_b(f o p^b_a) = mu_a(f) mu_{b-a}(1) = mu_a(f) of Federer
    2.6.6, p. 120, for a subset b and f in K(X_a). *)
Theorem finite_product_marginal_restriction (F G : {fset I}) (hFG : {subset F <= G})
    (f : finite_coordinate_space Y F -> R) :
  compactly_supported_continuous_functions f ->
  finite_coordinate_marginal C G (f \o finite_coordinate_restriction hFG)=
    finite_coordinate_marginal C F f*finite_coordinate_marginal C (G `\` F) (fun _=>1) /\
  finite_coordinate_marginal C F f*finite_coordinate_marginal C (G `\` F) (fun _=>1)=
    finite_coordinate_marginal C F f.
Proof. exact: (@finite_coordinate_marginal_restriction R I Y A hh hc hA hA1 C hC F G hFG f). Qed.
End Identification.
