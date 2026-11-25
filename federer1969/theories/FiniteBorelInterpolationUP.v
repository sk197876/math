(** Federer (1969), 2.2.15, p. 71, final criterion: abstract finite
    interpolation used to test its necessity on the real source. This
    supporting object records only the Borel property and attainment of the
    prescribed finite set. *)
From mathcomp Require Import all_boot classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground BorelFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_finite_borel_interpolation]: supporting laws
    for the necessity proof of Federer 2.2.15, p. 71.
    Every prescribed target value is attained on a finite set
    of real inputs by one Borel map. *)
Record is_finite_borel_interpolation (R : realType) (Y : topologicalType)
    (Z : set Y) (f : real_line_metric R -> Y) (F : set (real_line_metric R)) : Prop := {
  finite_interpolation_inputs : finite_set F;
  finite_interpolation_borel : is_borel_function f;
  finite_interpolation_covers : Z `<=` f @` F
}.
