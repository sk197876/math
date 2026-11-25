(** Federer (1969), 4.1.26, p. 383:
    every determinant sign of a positive-dimensional
    constant map is zero, including its
    entire critical fibre. The original numerical
    sum of these zero terms is zero
    even when that fibre is infinite. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps PartialFunctionUP NonnegativeSum NonnegativeSumSupport NumericalSum
  LipschitzDegreeSealed LipschitzDegreeFibreGraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_euclidean_zero_determinant]: the
    zero linear map has zero determinant
    in positive dimension, from 1.3.4, p. 16,
    supporting the critical-map case of 4.1.26,
    p. 383. The dimension-zero determinant
    retains its separate empty-product value one. *)
Lemma positive_euclidean_zero_determinant (R:realType) p:
  @euclidean_det R p.+1 (hom_as_linear (0:Hom (R_n R p.+1) (R_n R p.+1)))=0.
Proof.
apply/eqP;apply/negP=>hNonzero.
have hDetNonzero:@euclidean_det R p.+1
    (hom_as_linear (0:Hom (R_n R p.+1) (R_n R p.+1)))!=0.
  apply/negP;exact:hNonzero.
have hInjective:injective (hom_as_linear (0:Hom (R_n R p.+1) (R_n R p.+1))):=
  (@euclidean_det_injective R p.+1 _).1 hDetNonzero.
have hEquality:(@coordinate_basis R p.+1 ord0)=0.
  apply:hInjective;by rewrite !hom_as_linearE !hom_zeroE.
have hOne:=congr1 (fun x:R_n R p.+1=>x ord0) hEquality.
rewrite /coordinate_basis ffunE eqxx ffunE in hOne.
have hNot:(1:R)!=0:=oner_neq0 R;by rewrite hOne eqxx in hNot.
Qed.

(** Source for [lipschitz_degree_positive_constant_value]:
    the original signed degree of a
    positive-dimensional constant map is zero
    at every target point, including the
    nonempty critical fibre, supporting 4.1.26,
    p. 383. No source measurability is
    needed for this exact zero-sum calculation. *)
Theorem lipschitz_degree_positive_constant_value (R:realType) p
    (b:R_n R p.+1) (A:set (R_n R p.+1)) y:
  partial_function_graph (@LipschitzDegree.value R p.+1 (fun _=>b) A) y 0.
Proof.
apply:(@lipschitz_degree_fibre_graph R p.+1 (fun _=>b) A y 0).2.
exists (fun _=>0:R);split.
- move=>x _ _;exists 0;split.
  + exact:(@norm_differential_constant R (R_n R p.+1) (R_n R p.+1)
      (inner_norm (@euclidean_inner_productP R p.+1))
      (inner_norm (@euclidean_inner_productP R p.+1))
      (inner_norm_real_norm (@euclidean_inner_productP R p.+1))
      (inner_norm_real_norm (@euclidean_inner_productP R p.+1)) (fun _=>True) x b
      (norm_full_domain_interior _ x)).
  + by rewrite positive_euclidean_zero_determinant sgr0.
- rewrite numerical_sum_nonnegative;last by move=>x hx;exact:Order.POrderTheory.lexx.
  by rewrite nonnegative_sum_zero.
Qed.
