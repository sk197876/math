(** Federer (1969), 3.2.28(1), printed p. 263: the actual
    Euclidean ambient space Hom(R^m,R^n) has inner product 1.7.9
    and dimension mn. Coordinate choices are exposed only by
    proved finite-inner-chart existence. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerNorm HilbertFormCompactness
  HomInner LinearBasis HomCompositionDeterminant FiniteInnerChartUP FiniteInnerChart
  EuclideanHomOperator EuclideanGramDifferentialAlgebra EuclideanGramSmooth
  FiniteNormCalculusTransport NormRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_hom_inner_product]: the inner product
    on Hom in Federer 3.2.28(1), p. 263, as prescribed by
    1.7.9, p. 35. This is the existing opaque product interface. *)
Definition euclidean_hom_inner_product (R:realType) m n:=
  hom_inner (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    (@coordinate_basisP R m).

(** Source for [euclidean_hom_inner_productP]: the inner-product
    laws on the actual Hom ambient space, 1.7.9, p. 35,
    used in Federer 3.2.28(1), p. 263. *)
Lemma euclidean_hom_inner_productP (R:realType) m n:
  is_inner_product (@euclidean_hom_inner_product R m n).
Proof. exact:hom_inner_productP. Qed.

(** Source for [euclidean_hom_inner_chart_exists]: Hom(R^m,R^n)
    is a Euclidean space of dimension mn, Federer 3.2.28(1),
    p. 263. The rank-one basis of 1.4.5 and the abstract
    chart existence theorem give the correct Hilbert metric. *)
Theorem euclidean_hom_inner_chart_exists (R:realType) m n:
  exists (e:Hom (R_n R (m*n)) (Hom (R_n R m) (R_n R n)))
    (p:Hom (Hom (R_n R m) (R_n R n)) (R_n R (m*n))),
    is_finite_inner_chart (@euclidean_hom_inner_product R m n) e p.
Proof.
have hCard:#|{: 'I_m*'I_n}|= (m*n)%N by rewrite card_prod !card_ord.
rewrite -hCard.
apply:(finite_inner_chart_exists (@euclidean_hom_inner_productP R m n)).
exact:
  (@hom_rank_one_baseP R (R_n R m) (R_n R n) m n
    (@coordinate_basis R m) (@coordinate_basisP R m)
    (@coordinate_basis R n) (@coordinate_basisP R n)).
Qed.

(** Source for [euclidean_gram_inner_smooth]: smoothness of
    P for the actual inner product on Hom, Federer 3.2.28(1),
    p. 263. Norm equivalence transports the previously proved
    operator-norm calculus; it does not change the geometric metric. *)
Theorem euclidean_gram_inner_smooth (R:realType) m n:
  norm_class_all_orders
    (inner_norm_real_norm (@euclidean_hom_inner_productP R m n))
    (inner_norm_real_norm (@euclidean_hom_inner_productP R m m))
    (fun _=>True) (@euclidean_gram_map R m n).
Proof.
move=>k.
apply:(@norm_class_finite_norm_change R (Hom (R_n R m) (R_n R n))
  (Hom (R_n R m) (R_n R m)) (@euclidean_operator_norm R m n)
  (inner_norm (@euclidean_hom_inner_productP R m n))
  (@euclidean_operator_norm R m m)
  (inner_norm (@euclidean_hom_inner_productP R m m))
  (@euclidean_operator_norm_is_norm R m n)
  (inner_norm_real_norm (@euclidean_hom_inner_productP R m n))
  (@euclidean_operator_norm_is_norm R m m)
  (inner_norm_real_norm (@euclidean_hom_inner_productP R m m)) _ _
  (@hom_rank_one_baseP R (R_n R m) (R_n R n) m n
    (@coordinate_basis R m) (@coordinate_basisP R m)
    (@coordinate_basis R n) (@coordinate_basisP R n))
  _ _ (@hom_rank_one_baseP R (R_n R m) (R_n R m) m m
    (@coordinate_basis R m) (@coordinate_basisP R m)
    (@coordinate_basis R m) (@coordinate_basisP R m))).
exact:euclidean_gram_smooth.
Qed.
