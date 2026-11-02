(** Federer (1969), 2.2.15, p. 70: every Baire function is a Borel function,
    since Borel functions contain the continuous generators and are
    sequentially closed under pointwise limits. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import BorelFunctionUP BorelFunctionBasic BorelPointwiseLimits
  BaireFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [baire_function_borel]: direct inclusion in
    Federer 2.2.15, p. 70, obtained from the printed
    smallest-class definition and the proof referenced in 2.3.2(6),
    pp. 73–74. No separability hypothesis is needed. *)
Theorem baire_function_borel (R : realType) (X : topologicalType) (Y : metricType R)
    (f : X -> Y) : is_baire_function f -> is_borel_function f.
Proof.
apply: (@baire_function_induction R X Y (@is_borel_function X Y)).
- exact: borel_functions_pointwise_closed.
- move=> g hg; exact: continuous_borel_function hg.
Qed.
