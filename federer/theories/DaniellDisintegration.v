(** Public disintegration interface for Federer (1969), 2.5.20, p. 114.
    Downstream results use the abstract measure, kernel, support, and
    variation laws, without inspecting the function-space or density
    constructions. Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP DaniellIntegralUP
  DaniellSpaceWeakTopology DaniellDisintegrationUP DaniellDisintegrationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [daniell_disintegration_measure_value]: the
    Radon measure Phi of Federer 2.5.20, p. 114. *)
Definition daniell_disintegration_measure_value (R : realType) (X Y : metricType R)
  (mu : ((X*Y) -> R) -> R) (hX : compact (@setT X)) (hY : compact (@setT Y))
  (hmu : is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) mu) :=
  (@DaniellDisintegration.value R X Y mu hX hY hmu).1.

(** Source for [daniell_disintegration_kernel]: the measurable
    family of Daniell integrals k in Federer 2.5.20, p. 114. *)
Definition daniell_disintegration_kernel (R : realType) (X Y : metricType R)
  (mu : ((X*Y) -> R) -> R) (hX : compact (@setT X)) (hY : compact (@setT Y))
  (hmu : is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) mu) :=
  (@DaniellDisintegration.value R X Y mu hX hY hmu).2.

(** Source for [compact_metric_daniell_disintegration]: the
    first paragraph of Federer 2.5.20, p. 114, including
    the support conclusion and the defining variation of Phi. *)
Theorem compact_metric_daniell_disintegration (R : realType) (X Y : metricType R)
  (mu : ((X*Y) -> R) -> R) (hX : compact (@setT X)) (hY : compact (@setT Y))
  (hmu : is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) mu) :
  is_daniell_disintegration mu (daniell_disintegration_measure_value hX hY hmu)
    (daniell_disintegration_kernel hX hY hmu).
Proof. exact: DaniellDisintegration.laws. Qed.
