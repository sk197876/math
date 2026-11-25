(** Federer (1969), 4.1.23, p. 379:
    apply the attained simple-vector decomposition of
    1.8.1 to each constant positive-degree step value.
    Its exact mass cost is retained before
    rotating simple directions. Degree zero is treated
    separately by the original scalar sign convention. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals.
From Federer Require Import RealNormUP InnerProductUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates ExteriorGrading AssociatedSubspace ExteriorNorm
  Comass Mass MassEquality MassOptimalDecomposition CurrentCoefficientNorms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_vector_optimal_simple_decomposition]:
    the exact constant-value decomposition in
    the step reduction of Federer 4.1.23,
    p. 379, by 1.8.1, p. 38.
    The number of terms has the original
    binomial bound, and zero has the allowed
    empty decomposition. No approximation of the
    optimal mass cost is used. *)
Theorem current_vector_optimal_simple_decomposition (R : realType)
    (h2 : (1+1:R)!=0) n j (v : exterior_power (R_n R n) j.+1) :
  exists k, exists u : 'I_k -> exterior_power (R_n R n) j.+1,
    (k<='C(n,j.+1))%N /\ (forall i, simple (u i)) /\
    v=\sum_i u i /\
    @current_vector_mass R h2 n j.+1 v=
      \sum_i @current_vector_mass R h2 n j.+1 (u i) /\
    forall i, @current_vector_mass R h2 n j.+1 (u i)=
      @exterior_norm R h2 (R_n R n) (@euclidean_inner_product R n)
        (@euclidean_inner_productP R n) j.+1 (u i).
Proof.
pose X := R_n R n.
pose B := @euclidean_inner_product R n.
pose hB := @euclidean_inner_productP R n.
pose e := @coordinate_basis R n.
pose he := @coordinate_basisP R n.
pose m := j.+1.
pose hm := ltn0Sn j.
pose kappa := @comass R h2 X B hB n e he m hm.
pose hk := @comassP R h2 X B hB n e he m hm.
pose N := @exterior_norm R h2 X B hB m.
have [k [u [hCount [hSimple [hValue hCost]]]]] :=
  @mass_optimal_simple_decomposition R h2 X B hB n e he m hm
    kappa hk v (@current_vector_mass R h2 n m v)
    (@massP R h2 X B hB n e he m hm v).
have hMass i : @current_vector_mass R h2 n m (u i)=N (u i).
  exact: (@simple_mass_euclidean R h2 X B hB n e he m hm
    kappa hk (u i) (@current_vector_mass R h2 n m (u i))
    (hSimple i) (@massP R h2 X B hB n e he m hm (u i))).
exists k,u; split; first exact: hCount.
split; first exact: hSimple.
split; first exact: hValue.
split; last exact: hMass.
rewrite hCost; apply: eq_bigr=> i _; exact: esym (hMass i).
Qed.
