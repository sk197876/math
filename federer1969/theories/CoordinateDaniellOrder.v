(** Federer (1969), 2.6.6, p. 120: monotonicity and normalization persist
    under coordinate integrations. These are supporting laws of the finite
    products constructed by 2.6.4. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CoordinateDaniellOperator CompactSupportFunctionUP MonotoneDaniellIntegralUP FunctionLatticeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_daniell_operator_monotone]: order
    preservation under one factor integration, supporting the monotone
    finite products in Federer 2.6.6, p. 120. *)
Lemma coordinate_daniell_operator_monotone (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R) (i : I) :
  compact (@setT (Y i)) ->
  is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i) ->
  forall f g, compactly_supported_continuous_functions f -> compactly_supported_continuous_functions g ->
    function_le f g -> function_le (coordinate_daniell_operator A i f) (coordinate_daniell_operator A i g).
Proof.
move=> hc hA f g hf hg hfg x.
apply: (@monotone_daniell_integral_monotone R (Y i) _ (A i) hA _ _
  (@coordinate_daniell_section_membership R I Y i f x hc hf) (@coordinate_daniell_section_membership R I Y i g x hc hg))=> u.
exact: hfg.
Qed.

(** Source for [coordinate_daniell_operator_one]: a factor of mass
    one fixes the constant 1, supporting Federer 2.6.6, p. 120. *)
Lemma coordinate_daniell_operator_one (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R) (i : I) :
  A i (fun _=>1) = 1 -> coordinate_daniell_operator A i (fun _=>1)=(fun _=>1).
Proof. by move=> hA; apply: funext=> x; exact: hA. Qed.
