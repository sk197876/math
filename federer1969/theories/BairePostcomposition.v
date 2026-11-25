(** Federer (1969), 2.2.15, pp. 70–71: continuous postcomposition preserves
    Baire functions, supporting the real algebra argument and the final
    metric-target criterion. The proof uses minimality and pointwise
    continuity, with no appeal to a preconstructed hierarchy or Baire ranks.
    Composites use explicit pointwise application to avoid the fixed
    universes of the standard composition constant when importing this
    module together with the Chapter 1 development. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import PointwiseLimit BaireFunctionUP BaireFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [baire_continuous_postcomposition]: supporting
    closure under continuous target maps for Federer 2.2.15,
    pp. 70–71. The class of maps whose composites
    are Baire contains the continuous maps and is sequentially
    closed, so the smallest-class property applies. *)
Theorem baire_continuous_postcomposition (R : realType) (X : topologicalType)
    (Y Z : metricType R) (h : Y -> Z) : continuous h ->
  forall f : X -> Y, is_baire_function f -> is_baire_function (fun x => h (f x)).
Proof.
move=> hh; apply: (@baire_function_induction R X Y
  [set f | is_baire_function (fun x => h (f x))]).
- move=> f g hf hlim; apply: (@baire_function_pointwise_limit R X Z
    (fun n x => h (f n x)) (fun x => h (g x)))=> //.
  exact: pointwise_limit_continuous_postcomposition hlim hh.
- move=> f hf; apply: continuous_baire_function=> x.
  exact: continuous_comp (hf x) (hh (f x)).
Qed.
