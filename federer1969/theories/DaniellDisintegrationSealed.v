(** Opaque disintegration for Federer (1969), 2.5.20, p. 114. The
    representing measure, kernel, and variation specification are exposed;
    their choices and function-space realization remain private. Source
    context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP DaniellIntegralUP
  DaniellSpaceWeakTopology DaniellDisintegrationUP DaniellDisintegrationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

Module Type DaniellDisintegrationSignature.
(** Source for [value]: the pair consisting of Phi and k
    in Federer 2.5.20, p. 114. *)
Parameter value : forall (R : realType) (X Y : metricType R)
  (mu : ((X*Y) -> R) -> R), compact (@setT X) -> compact (@setT Y) ->
  is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) mu ->
  ((set X -> \bar R) * (X -> daniell_weak_space
    (@compactly_supported_continuous_functions R Y)))%type.
(** Source for [laws]: the full first-paragraph conclusions
    and the specified variation measure, Federer 2.5.20, p. 114. *)
Parameter laws : forall (R : realType) (X Y : metricType R)
  (mu : ((X*Y) -> R) -> R) (hX : compact (@setT X)) (hY : compact (@setT Y))
  (hmu : is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) mu),
  is_daniell_disintegration mu (@value R X Y mu hX hY hmu).1 (@value R X Y mu hX hY hmu).2.
End DaniellDisintegrationSignature.

Module DaniellDisintegration : DaniellDisintegrationSignature.
(** Source for [value]: private selection from the verified
    disintegration existence theorem, Federer 2.5.20, p. 114. *)
Definition value (R : realType) (X Y : metricType R)
  (mu : ((X*Y) -> R) -> R) (hX : compact (@setT X)) (hY : compact (@setT Y))
  (hmu : is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) mu) :=
  sval (cid (@daniell_disintegration_pair_exists R X Y mu hX hY hmu)).
(** Source for [laws]: the selected witness satisfies its
    abstract disintegration laws, Federer 2.5.20, p. 114. *)
Lemma laws (R : realType) (X Y : metricType R)
  (mu : ((X*Y) -> R) -> R) (hX : compact (@setT X)) (hY : compact (@setT Y))
  (hmu : is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) mu) :
  is_daniell_disintegration mu (@value R X Y mu hX hY hmu).1 (@value R X Y mu hX hY hmu).2.
Proof. exact: svalP (cid (@daniell_disintegration_pair_exists R X Y mu hX hY hmu)). Qed.
End DaniellDisintegration.
