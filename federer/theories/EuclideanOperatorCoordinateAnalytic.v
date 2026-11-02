(** Federer (1969), 3.2.33, p. 270: scalar coordinates
    of the differential in the exterior Gram polynomials h_i.
    The analyticity proof uses bounded linear evaluation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness EuclideanCoordinateMetric RealNormUP
  NormDifferentialUP NormOperatorNormUP ContinuousOperatorUP EuclideanHomOperator
  NormAnalyticUP NormAnalyticLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_operator_coordinate_analytic]: the
    matrix entries used to expand h_i in Federer 3.2.33,
    p. 270, are analytic functions on the actual Hom space
    with its operator norm. The estimate holds for any fixed
    source vector, including zero and zero ambient dimensions. *)
Theorem euclidean_operator_coordinate_analytic (R:realType) m n
    (v:R_n R m) (j:'I_n):
  @norm_analytic R (Hom (R_n R m) (R_n R n)) R^o
    (@euclidean_operator_norm R m n) (fun t:R^o=>`|t|)
    (@euclidean_operator_norm_is_norm R m n) (@scalar_absolute_value_norm R)
    setT (fun L=>(L v) j).
Proof.
have hLinear:linear (fun L:Hom (R_n R m) (R_n R n)=>(L v) j).
  move=>c L M; by rewrite hom_addE hom_scaleE !ffunE.
pose E:=@HomMap R (Hom (R_n R m) (R_n R n)) R^o
  (fun L=>(L v) j) (introT (asboolP _) hLinear).
have hBound:norm_bounded_linear (@euclidean_operator_norm R m n)
    (fun t:R^o=>`|t|) E.
  exists (inner_norm (@euclidean_inner_productP R m) v); split.
  - exact:inner_norm_nonnegative.
  - move=>L; change (is_true (`|(L v) j|<=
      inner_norm (@euclidean_inner_productP R m) v*euclidean_operator_norm L)).
    apply:le_trans (euclidean_coordinate_norm_bound j (L v)) _.
    rewrite mulrC.
    exact:(norm_operator_bound
      (continuous_operator_norm_laws (@euclidean_hom_operator_space R m n) L) v).
apply:(@norm_bounded_linear_analytic R (Hom (R_n R m) (R_n R n)) R^o
  (@euclidean_operator_norm R m n) (fun t:R^o=>`|t|)
  (@euclidean_operator_norm_is_norm R m n) (@scalar_absolute_value_norm R)
  setT _ E hBound).
move=>L _; exists 1; split; first exact:ltr01; by move=>M hM.
Qed.
