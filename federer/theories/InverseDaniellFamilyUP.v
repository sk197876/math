(** Federer (1969), 2.6.6, pp. 120–121, final paragraph: consistency of
    Daniell integrals under the bonding maps. Normalization and monotonicity
    retain the standing hypotheses of the discussion on p. 120. No extension
    is postulated. Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP MonotoneDaniellIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_consistent_inverse_daniell_family]: abstract
    compatibility of normalized monotone functionals in the
    inverse-limit paragraph of Federer 2.6.6, pp. 120–121. *)
Record is_consistent_inverse_daniell_family (R : realType) (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
    (A : forall i, (Y i -> R) -> R) : Prop := {
  (** Source for [inverse_daniell_family_integral]: the factor
      Daniell laws retained from Federer 2.6.6, p. 120. *)
  inverse_daniell_family_integral : forall i,
    is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i);
  (** Source for [inverse_daniell_family_one]: normalization
      retained from Federer 2.6.6, p. 120. *)
  inverse_daniell_family_one : forall i, A i (fun _=>1) = 1;
  (** Source for [inverse_daniell_family_consistent]: the
      pushforward consistency equation of Federer 2.6.6,
      pp. 120–121, for arbitrary comparable indices. *)
  inverse_daniell_family_consistent : forall i j, le i j -> forall f,
    compactly_supported_continuous_functions f -> A j (f \o b i j)=A i f
}.

(** Source for [is_inverse_limit_daniell_integral]: abstract
    marginal characterization of the inverse-limit integral
    suggested by the last paragraph of Federer 2.6.6,
    pp. 120–121, under its normalized monotone hypotheses. *)
Definition is_inverse_limit_daniell_integral (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (X : topologicalType) (p : forall i, X -> Y i)
    (A : forall i, (Y i -> R) -> R) (B : (X -> R) -> R) :=
  is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) B /\
  B (fun _=>1) = 1 /\ forall i f, compactly_supported_continuous_functions f -> B (f \o p i)=A i f.
