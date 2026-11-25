(** Public inverse-limit integral, Federer (1969), 2.6.6, pp. 120–121. The
    definition uses only the sealed interface. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactInverseSystemUP CompactInverseLimitUP InverseDaniellFamilyUP InverseDaniellIntegralSealed InverseDaniellExtensionUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(** Source for [inverse_limit_daniell_integral]: the unique
    normalized monotone Daniell functional with the prescribed
    coordinate marginals, Federer 2.6.6, pp. 120–121. *)
Definition inverse_limit_daniell_integral (R : realType) (I : choiceType) (le : I -> I -> Prop)
  (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
  (X : topologicalType) (p : forall i, X -> Y i)
  (A : forall i, (Y i -> R) -> R)
  (hs : is_compact_inverse_system le b) (hl : is_compact_inverse_limit le b p)
  (hA : is_consistent_inverse_daniell_family le b A) :=
  @InverseDaniellIntegral.value R I le Y b X p A hs hl hA.
(** Source for [inverse_limit_daniell_integral_specification]:
    the exposed marginal and Daniell laws, Federer 2.6.6,
    pp. 120–121. *)
Lemma inverse_limit_daniell_integral_specification (R : realType) (I : choiceType) (le : I -> I -> Prop)
  (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
  (X : topologicalType) (p : forall i, X -> Y i)
  (A : forall i, (Y i -> R) -> R)
  (hs : is_compact_inverse_system le b) (hl : is_compact_inverse_limit le b p)
  (hA : is_consistent_inverse_daniell_family le b A) :
  is_inverse_limit_daniell_integral p A (@inverse_limit_daniell_integral R I le Y b X p A hs hl hA).
Proof. exact: InverseDaniellIntegral.laws. Qed.
