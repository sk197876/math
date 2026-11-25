(** Federer (1969), 4.1.12, p. 369: the
    separated test and its exterior differential have
    the exact preceding binomial comass bounds. Reuse
    4.1.8's product and Leibniz law, including both
    zero degrees, rather than a new coordinate proof. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap CurrentSpaces CurrentCoefficientNorms
  CurrentCartesianDomain CurrentCartesianTestProductUP CurrentCartesianTestProductSealed
  CurrentCartesianCovectorBinomial CurrentCartesianTestExteriorLeibniz CurrentTestExteriorDerivative
  CurrentDegreeTransport CurrentTestDegreeComass CurrentTestValueLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianTestComass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation DA k := (@current_test_space R h2 m A hA k).
Local Notation DB k := (@current_test_space R h2 n B hB k).
Local Notation va k := (@current_test_value R h2 m A hA k).
Local Notation vb k := (@current_test_value R h2 n B hB k).
Local Notation vc k := (@current_test_value R h2 (m+n) AB hAB k).
Local Notation NA k := (@current_form_comass R h2 m k).
Local Notation NB k := (@current_form_comass R h2 n k).
Local Notation NC k := (@current_form_comass R h2 (m+n) k).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).
Local Notation Pure k l := (@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation dA k := (@current_test_exterior_derivative R h2 m k A hA).
Local Notation dB k := (@current_test_exterior_derivative R h2 n k B hB).
Local Notation dC k := (@current_test_exterior_derivative R h2 (m+n) k AB hAB).

(** Source for [current_cartesian_test_comass_bound]:
    the original pure test has comass at most
    binomial(i+j,i) times the factor comasses,
    supporting Federer 4.1.12, p. 369,
    by the preceding 4.1.8 estimate on p. 361. *)
Theorem current_cartesian_test_comass_bound i j (alpha:DA i) (beta:DB j) z:
  AB z->NC (i+j) (vc (i+j) (Pure i j alpha beta) z)<=
    'C(i+j,i)%:R * (NA i (va i alpha (p z)) * NB j (vb j beta (q z))).
Proof.
move=>hz;rewrite ((@CartesianTestProduct.laws R h2 m n A B hA hB i j).2 alpha beta z hz).
exact:current_cartesian_covector_binomial_bound.
Qed.

(** Source for [current_cartesian_test_derivative_comass_bound]:
    d of the pure test satisfies the sum of the
    two adjacent binomial bounds. Their Pascal sum
    is the printed coefficient binomial(i+j+2,i+1)
    in Federer 4.1.12, p. 369. *)
Theorem current_cartesian_test_derivative_comass_bound i j (alpha:DA i) (beta:DB j) z:
  AB z->NC (i+j).+1 (vc (i+j).+1 (dC (i+j) (Pure i j alpha beta)) z)<=
    'C(i.+1+j,i.+1)%:R * (NA i.+1 (va i.+1 (dA i alpha) (p z)) * NB j (vb j beta (q z)))+
    'C(i+j.+1,i)%:R * (NA i (va i alpha (p z)) * NB j.+1 (vb j.+1 (dB j beta) (q z))).
Proof.
move=>hz;rewrite (@current_cartesian_test_exterior_leibniz R h2 m n A B hA hB i j alpha beta)
  current_test_add_value current_test_scale_value.
have hNorm:=@current_form_comass_real_norm R h2 (m+n) (i+j).+1.
apply:(le_trans (real_seminorm_triangle hNorm.1 _ _)).
rewrite (real_seminorm_scale hNorm.1) normrX normrN normr1 expr1n mul1r
  !current_test_degree_transport_comass.
apply:lerD;exact:current_cartesian_test_comass_bound.
Qed.
End CurrentCartesianTestComass.
