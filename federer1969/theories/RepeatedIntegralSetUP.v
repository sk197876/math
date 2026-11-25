(** Federer (1969), 2.6.2, p. 115, proof: the family F consists of sets
    whose characteristic functions have an iterated integral, first over X
    and then over Y. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic CharacteristicFunctionUP
  MeasureIntegralUP ParameterizedIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [is_repeatedly_integrable_set]: direct family F
    in Federer 2.6.2, p. 115, retained in 2.6.3(3),
    p. 118. The characteristic function is specified by its laws;
    inner integrals keep their actual domains. Infinite values of
    the repeated integral are allowed, as for the rectangles in F
    on p. 116. No product measurability is built into this family. *)
Definition is_repeatedly_integrable_set (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (S : set (X * Y)) :=
  exists (s : X * Y -> R) a, is_characteristic_function S s /\
    is_measure_integral beta (parameterized_integral alpha
      (fun y => partial_function_total (fun x => (s (x,y))%:E))) a.
