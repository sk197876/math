(** Federer (1969), 2.2.7, p. 64: public least Lipschitz constant, using
    only the sealed attainment and minimality laws. Source context and
    zero-bound convention: LipschitzUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import LipschitzUP LipschitzConstantSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_lipschitz_constant]: Federer 2.2.7,
    p. 64, the notation Lip(f), exposed through its abstract laws.
    A Lipschitzian hypothesis makes this value finite. *)
Definition metric_lipschitz_constant (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) (h : is_metric_lipschitz X f) : R :=
  LipschitzConstant.value h.

(** Source for [metric_lipschitz_constant_specification]: Federer 2.2.7, p.
    64: Lip(f) is the least attained nonnegative bound *)
Lemma metric_lipschitz_constant_specification (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) (h : is_metric_lipschitz X f) :
  is_least_metric_lipschitz_constant X f (metric_lipschitz_constant h).
Proof. exact: LipschitzConstant.laws. Qed.

(** Source for [metric_lipschitz_constant_nonnegative]: supporting boundary
    convention for Federer 2.2.7, p. 64. *)
Lemma metric_lipschitz_constant_nonnegative (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) (h : is_metric_lipschitz X f) :
  0 <= metric_lipschitz_constant h.
Proof. exact: (proj1 (least_metric_lipschitz_bound (metric_lipschitz_constant_specification h))). Qed.

(** Source for [metric_lipschitz_constant_attained]: Federer 2.2.7, p. 64,
    attainment of Lip(f) in the printed distance inequality *)
Lemma metric_lipschitz_constant_attained (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) (h : is_metric_lipschitz X f) x y :
  X x -> X y -> mdist (f x) (f y) <= metric_lipschitz_constant h * mdist x y.
Proof. exact: (proj2 (least_metric_lipschitz_bound (metric_lipschitz_constant_specification h)) x y). Qed.

(** Source for [metric_lipschitz_constant_minimal]: Federer
    2.2.7, p. 64, minimality of Lip(f) among admissible bounds. *)
Lemma metric_lipschitz_constant_minimal (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) (h : is_metric_lipschitz X f) M :
  is_metric_lipschitz_bound X f M -> metric_lipschitz_constant h <= M.
Proof. exact: (least_metric_lipschitz_minimal (metric_lipschitz_constant_specification h)). Qed.
