(** Federer (1969), 2.6.6, pp. 120–121, last paragraph: "The same type of
    reasoning can be applied to arbitrary inverse limits of Daniell
    integrals on lattices of continuous functions on compact Hausdorff
    spaces." This file extends the uniqueness half of that reasoning: the
    inverse-limit integral of a consistent family of normalised monotone
    Daniell integrals is the only Daniell integral on K(X), monotone or not,
    with the prescribed coordinate marginals. The existence half keeps the
    normalised monotone hypotheses of the discussion on p. 120. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP DaniellIntegralUP CompactInverseSystemUP
  CompactInverseLimitUP InverseDaniellFamilyUP InverseDaniellIntegral InverseDaniellContinuousExtension
  CompactContinuousPullback CompactDaniellUniformContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Characterization.
Variables (R : realType) (I : choiceType) (le : I -> I -> Prop).
Variables (Y : I -> topologicalType) (b : forall i j, Y j -> Y i).
Variables (X : topologicalType) (p : forall i, X -> Y i) (A : forall i, (Y i -> R) -> R).
Variables (hs : is_compact_inverse_system le b) (hl : is_compact_inverse_limit le b p)
  (hA : is_consistent_inverse_daniell_family le b A).
Local Notation K := (@compactly_supported_continuous_functions R X).
Local Notation mu := (@inverse_limit_daniell_integral R I le Y b X p A hs hl hA).

(** Source for [has_inverse_limit_marginals]: the condition
    p_i#(D) = A_i for every index i, the inverse-limit form of
    "p_a#(mu) = mu_a whenever a in A", Federer 2.6.6, pp. 120–121. *)
Definition has_inverse_limit_marginals (D : (X -> R) -> R) :=
  forall i f, compactly_supported_continuous_functions f -> D (f \o p i)=@A i f.

(** Source for [inverse_limit_daniell_integral_daniell_unique]:
    uniqueness of the inverse-limit integral among all Daniell
    integrals on K(X), Federer 2.6.6, pp. 120–121. The competitor
    need not be monotone or normalised. *)
Theorem inverse_limit_daniell_integral_daniell_unique (D : (X -> R) -> R) :
  is_daniell_integral K D -> has_inverse_limit_marginals D -> forall f, K f -> D f=mu f.
Proof.
move=> hD hDm.
apply: (@inverse_limit_continuous_extension_unique R I le Y b X p A hs hl hA D _ hDm).
exact: compact_daniell_uniform_continuous (compact_inverse_limit_compact hl) hD.
Qed.

(** Source for [inverse_limit_daniell_integral_daniell_characterization]:
    for every Daniell integral D on K(X), D has the coordinate
    marginals A_i if and only if D agrees with the inverse-limit
    integral on K(X), Federer 2.6.6, pp. 120–121. *)
Theorem inverse_limit_daniell_integral_daniell_characterization (D : (X -> R) -> R) :
  is_daniell_integral K D -> (has_inverse_limit_marginals D <-> forall f, K f -> D f=mu f).
Proof.
move=> hD; split; first exact: inverse_limit_daniell_integral_daniell_unique.
move=> he i f hf.
have hB := @inverse_limit_daniell_integral_specification R I le Y b X p A hs hl hA.
have hfp : K (f \o p i).
  exact: (@compact_continuous_pullback_membership R X (Y i) (p i) f (compact_inverse_limit_compact hl)
    (@compact_inverse_limit_projection_continuous I le Y b X p hl i) hf).
rewrite (he _ hfp); exact: hB.2.2 i f hf.
Qed.

(** Source for [inverse_limit_marginals_determine_daniell]: two
    Daniell integrals on K(X) with the same coordinate marginals A_i
    coincide on K(X), Federer 2.6.6, pp. 120–121. *)
Theorem inverse_limit_marginals_determine_daniell (B D : (X -> R) -> R) :
  is_daniell_integral K B -> is_daniell_integral K D ->
  has_inverse_limit_marginals B -> has_inverse_limit_marginals D -> forall f, K f -> B f=D f.
Proof.
move=> hB hD hBm hDm f hf.
by rewrite (inverse_limit_daniell_integral_daniell_unique hB hBm hf)
  (inverse_limit_daniell_integral_daniell_unique hD hDm hf).
Qed.
End Characterization.
