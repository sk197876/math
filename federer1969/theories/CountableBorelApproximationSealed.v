(** Federer (1969), 2.2.15, p. 71: opaque countable-range approximations,
    exposing Borel label fibres and reciprocal metric error only. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import BorelFunctionUP CountableBorelApproximationUP
  CountableBorelApproximationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CountableBorelApproximationSignature.
(** Source for [value]: abstract countable approximation
    data supporting Federer 2.2.15, p. 71. *)
Parameter value : forall (R : realType) (X : topologicalType) (Y : metricType R)
  (f : X -> Y) (y0 : Y) (D : set Y),
  countable D -> dense D -> is_borel_function f -> (nat -> Y) * (nat -> X -> nat).
(** Source for [laws]: Borel-fibre and metric-error
    laws supporting Federer 2.2.15, p. 71. *)
Parameter laws : forall (R : realType) (X : topologicalType) (Y : metricType R)
  (f : X -> Y) (y0 : Y) (D : set Y) (hc : countable D) (hd : dense D)
  (hf : is_borel_function f),
  is_countable_borel_approximation f (@value R X Y f y0 D hc hd hf).1
    (@value R X Y f y0 D hc hd hf).2.
End CountableBorelApproximationSignature.
Module CountableBorelApproximation : CountableBorelApproximationSignature.
(** Source for [value]: private selection of the proved
    approximation witness for Federer 2.2.15, p. 71. *)
Definition value (R : realType) (X : topologicalType) (Y : metricType R)
  (f : X -> Y) (y0 : Y) (D : set Y) (hc : countable D) (hd : dense D)
  (hf : is_borel_function f) :=
  let w := cid (@countable_borel_approximation_exists R X Y f y0 D hc hd hf) in
  (projT1 w, projT1 (cid (projT2 w))).
(** Source for [laws]: the selected data satisfy the
    abstract laws supporting Federer 2.2.15, p. 71. *)
Lemma laws (R : realType) (X : topologicalType) (Y : metricType R)
  (f : X -> Y) (y0 : Y) (D : set Y) (hc : countable D) (hd : dense D)
  (hf : is_borel_function f) :
  is_countable_borel_approximation f (@value R X Y f y0 D hc hd hf).1
    (@value R X Y f y0 D hc hd hf).2.
Proof. exact: projT2 (cid (projT2 (cid (@countable_borel_approximation_exists R X Y f y0 D hc hd hf)))). Qed.
End CountableBorelApproximation.
