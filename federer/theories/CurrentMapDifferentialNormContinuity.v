(** Federer (1969), 4.1.9, p. 364: the original
    endpoint differential norms in the affine mass
    integrals are continuous. This supporting adapter
    reuses the class-one field continuity of 3.1.1,
    p. 210, and its proved least-bound norm equivalence. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormMetricContinuity NormDifferentialUP NormClassOneUP
  NormClassOneLaws NormRegularity NormOperatorNormUP ContinuousOperatorUP EuclideanHomOperator
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentMapDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentMapDifferentialNormContinuity.
Variable R:realType.
Variables n nu:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation NOp := (@euclidean_operator_norm R n nu).
Local Notation hNOp := (@euclidean_operator_norm_is_norm R n nu).
Variable U:set X.
Variable f:X->Y.
Hypothesis hClass:norm_class hNX hNY U f 1%N.
Local Notation Actual := (@current_map_differential R n nu U f).

(** Source for [current_class_one_differential_continuous]:
    the actual sealed differential field is continuous
    in the original operator norm, supporting the affine
    integrals in Federer 4.1.9, p. 364, through
    the literal class-one condition of 3.1.1, p. 210. *)
Theorem current_class_one_differential_continuous:
  norm_class_zero NX NOp U Actual.
Proof.
have[D hD]:=(@norm_class_firstP R X Y NX NY hNX hNY U f).1 hClass.
have hSame x (hx:U x):D x=Actual x.
  exact:esym (@current_map_differential_unique R n nu U f x (D x)
    (norm_class_one_differential hD hx)).
have hField:norm_field_continuous NX NY U Actual.
  move=>a ha e he.
  have[d [hd hBound]]:=norm_class_one_continuity hD ha he.
  exists d;split=>// z hz hSmall v.
  rewrite -(hSame (a+z) hz) -(hSame a ha).
  exact:hBound z hz hSmall v.
have hSpec x a (hx:U x) (ha:U a):is_norm_operator_norm NX NY (Actual x-Actual a) (NOp (Actual x-Actual a)).
  exact:(continuous_operator_norm_laws (@euclidean_hom_operator_space R n nu) (Actual x-Actual a)).
have hOperator:=(@norm_field_continuous_operator R X Y NX NY hNX U Actual
  (fun x a=>NOp (Actual x-Actual a)) hSpec).1 hField.
move=>a ha;split;first exact:(@norm_class_one_zero R X Y NX NY U f D hD a ha).1.
exact:hOperator a ha.
Qed.

(** Source for [current_class_one_differential_norm_continuous]:
    the exact scalar ||Df|| is continuous on the
    original U, supporting the affine mass integrals
    in Federer 4.1.9, p. 364. No global extension
    of the original differential is claimed continuous. *)
Theorem current_class_one_differential_norm_continuous:
  norm_class_zero NX (fun t:R^o=>`|t|) U (fun x=>NOp (Actual x)).
Proof.
move=>a ha;have[hInterior hContinuous]:=@current_class_one_differential_continuous a ha.
split=>// e he;have[d [hd hBound]]:=hContinuous e he.
exists d;split=>// z hz hSmall.
exact:(le_lt_trans (@real_norm_change_bound R (Hom X Y) NOp hNOp
  (Actual (a+z)) (Actual a)) (hBound z hz hSmall)).
Qed.
End CurrentMapDifferentialNormContinuity.
