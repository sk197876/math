(** Opaque inverse-limit integral for Federer (1969), 2.6.6, pp. 120–121.
    Only normalized monotone Daniell and marginal laws are exposed. Source
    context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactInverseSystemUP CompactInverseLimitUP InverseDaniellFamilyUP InverseDaniellExtensionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type InverseDaniellIntegralSignature.
(** Source for [value]: the inverse-limit functional discussed
    in Federer 2.6.6, pp. 120–121, retaining normalization
    and monotonicity. *)
Parameter value : forall (R : realType) (I : choiceType) (le : I -> I -> Prop)
  (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
  (X : topologicalType) (p : forall i, X -> Y i)
  (A : forall i, (Y i -> R) -> R)
  (hs : is_compact_inverse_system le b) (hl : is_compact_inverse_limit le b p)
  (hA : is_consistent_inverse_daniell_family le b A), (X -> R) -> R.
(** Source for [laws]: normalized Daniell and marginal laws
    for the inverse-limit extension of Federer 2.6.6, pp. 120–121. *)
Parameter laws : forall (R : realType) (I : choiceType) (le : I -> I -> Prop)
  (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
  (X : topologicalType) (p : forall i, X -> Y i)
  (A : forall i, (Y i -> R) -> R)
  (hs : is_compact_inverse_system le b) (hl : is_compact_inverse_limit le b p)
  (hA : is_consistent_inverse_daniell_family le b A),
  is_inverse_limit_daniell_integral p A (@value R I le Y b X p A hs hl hA).
End InverseDaniellIntegralSignature.
Module InverseDaniellIntegral : InverseDaniellIntegralSignature.
(** Source for [value]: private choice from the proved
    inverse-limit existence result, Federer 2.6.6, pp. 120–121. *)
Definition value (R : realType) (I : choiceType) (le : I -> I -> Prop)
  (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
  (X : topologicalType) (p : forall i, X -> Y i)
  (A : forall i, (Y i -> R) -> R)
  (hs : is_compact_inverse_system le b) (hl : is_compact_inverse_limit le b p)
  (hA : is_consistent_inverse_daniell_family le b A) :=
  sval (cid (@inverse_limit_daniell_integral_exists R I le Y b X p A hs hl hA)).
(** Source for [laws]: the chosen witness obeys the exposed
    inverse-limit laws, Federer 2.6.6, pp. 120–121. *)
Lemma laws (R : realType) (I : choiceType) (le : I -> I -> Prop)
  (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
  (X : topologicalType) (p : forall i, X -> Y i)
  (A : forall i, (Y i -> R) -> R)
  (hs : is_compact_inverse_system le b) (hl : is_compact_inverse_limit le b p)
  (hA : is_consistent_inverse_daniell_family le b A) :
  is_inverse_limit_daniell_integral p A (@value R I le Y b X p A hs hl hA).
Proof. exact: svalP (cid (@inverse_limit_daniell_integral_exists R I le Y b X p A hs hl hA)). Qed.
End InverseDaniellIntegral.
