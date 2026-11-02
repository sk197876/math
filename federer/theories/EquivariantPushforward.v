(** Federer (1969), 2.7.2, printed p. 123: "These two cases are related by
    the commutative diagram ... We see that mu is a left chi covariant
    integral if and only if p#(mu) is a right chi covariant integral." The
    argument behind "We see" is general: let A and B be maps G -> X -> X and
    G -> Y -> Y, written as actions, and let p: X -> Y be a homeomorphism
    with inverse q such that p o A_g = B_g o p whenever g in G. Then p is
    continuous and proper, p# of 2.5.19, p. 113, is daniell_pushforward, and
    for u in K(Y) p#(mu)(u o B_g) = mu(u o p o A_g) = chi(g) p#(mu)(u).
    Since q o B_g = A_g o q and q#(p#(mu)) = mu, the converse follows by
    symmetry. Monotonicity and the property of not vanishing on K transfer
    in the same way. No group structure is used. HaarInversion.v applies
    these facts to the inversion of G. Neither. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import HomeomorphismUP MonotoneDaniellIntegralUP DaniellIntegralUP
  CompactSupportFunctionUP ProperMapUP DaniellSpacePushforward CovariantIntegralUP HaarIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [homeomorphism_with_inverse_proper]: a homeomorphism
    is proper, as required for p# in Federer 2.5.19, p. 113, applied to
    p(x) = x^{-1} in 2.7.2, p. 123: the inverse image of a compact set C
    under p is the compact set q(C), q the inverse of p. Supporting
    lemma. *)
Lemma homeomorphism_with_inverse_proper (S T : topologicalType) (p : S -> T) (q : T -> S) :
  is_homeomorphism_with_inverse p q -> is_proper_map p.
Proof.
move=> hpq C hC.
have hqp := homeomorphism_with_inverse_symmetric hpq.
rewrite -(homeomorphism_with_inverse_image C hqp).
apply: continuous_compact=> //; apply: continuous_subspaceT.
exact: homeomorphism_continuous hqp.
Qed.

Section Equivariant.
Variable R : realType.
Variable G : Type.
Variables X Y : topologicalType.
Variables (A : G -> X -> X) (B : G -> Y -> Y) (p : X -> Y) (q : Y -> X).
Hypothesis hpq : is_homeomorphism_with_inverse p q.
Hypothesis hAB : forall g x, p (A g x) = B g (p x).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation KY := (@compactly_supported_continuous_functions R Y).

(** Source for [equivariant_inverse_intertwines]: q o B_g = A_g o q,
    the inverse form of the commutative diagram of Federer 2.7.2,
    p. 123. Supporting lemma: q(B_g(y)) = q(B_g(p(q y))) =
    q(p(A_g(q y))) = A_g(q y). *)
Lemma equivariant_inverse_intertwines g y : q (B g y) = A g (q y).
Proof.
rewrite -[in LHS](homeomorphism_right_inverse hpq y) -hAB.
exact: (homeomorphism_left_inverse hpq (A g (q y))).
Qed.

(** Source for [equivariant_pushforward_cancel]: q#(p#(mu)) = mu,
    supporting the converse in Federer 2.7.2, p. 123: u o q o p = u for
    every function u on X. *)
Lemma equivariant_pushforward_cancel (mu : (X -> R) -> R) :
  daniell_pushforward q (daniell_pushforward p mu) = mu.
Proof.
apply: funext=> u; rewrite /daniell_pushforward; congr mu.
by apply: funext=> x; rewrite /= (homeomorphism_left_inverse hpq).
Qed.

(** Source for [equivariant_compactly_supported]: u o p is in K(X)
    whenever u in K(Y), for the homeomorphism p, supporting Federer
    2.5.19, p. 113, as used in 2.7.2, p. 123. *)
Lemma equivariant_compactly_supported (u : Y -> R) : KY u -> KX (u \o p).
Proof.
exact: (@compactly_supported_compose R X Y p (homeomorphism_continuous hpq)
  (homeomorphism_with_inverse_proper hpq) u).
Qed.

(** Source for [equivariant_covariant_on]: the implication "mu is a
    left chi covariant integral ... only if p#(mu) is a right chi
    covariant integral" of Federer 2.7.2, p. 123, for the covariance
    identity, in the general form: if mu(u o A_g) = chi(g) mu(u) for u in
    K(X), then p#(mu)(u o B_g) = chi(g) p#(mu)(u) for u in K(Y),
    because u o B_g o p = (u o p) o A_g. *)
Lemma equivariant_covariant_on (chi : G -> R) (mu : (X -> R) -> R) :
  is_covariant_on KX A chi mu -> is_covariant_on KY B chi (daniell_pushforward p mu).
Proof.
move=> hc u g hu; rewrite /daniell_pushforward.
have -> : (u \o B g) \o p = (u \o p) \o A g by apply: funext=> x; rewrite /= hAB.
exact: hc (equivariant_compactly_supported hu).
Qed.

(** Source for [equivariant_covariant_integral_forward]: the
    implication of Federer 2.7.2, p. 123, for chi covariant integrals
    in the general form: p# maps Daniell integrals on K(X) to Daniell
    integrals on K(Y) by 2.5.19, p. 113, and preserves covariance by
    equivariant_covariant_on. *)
Lemma equivariant_covariant_integral_forward (chi : G -> R) (mu : (X -> R) -> R) :
  is_covariant_integral A chi mu -> is_covariant_integral B chi (daniell_pushforward p mu).
Proof.
case=> hd hc; constructor; last exact: equivariant_covariant_on.
exact: (@daniell_pushforward_daniell R X Y p (homeomorphism_continuous hpq)
  (homeomorphism_with_inverse_proper hpq) mu hd).
Qed.

(** Source for [equivariant_monotone_forward]: p# maps monotone
    Daniell integrals on K(X) to monotone Daniell integrals on K(Y),
    Federer 2.5.19, p. 113, supporting the Haar integrals of 2.7.2,
    p. 122. *)
Lemma equivariant_monotone_forward (mu : (X -> R) -> R) :
  is_monotone_daniell_integral KX mu -> is_monotone_daniell_integral KY (daniell_pushforward p mu).
Proof.
exact: (@daniell_pushforward_monotone R X Y p (homeomorphism_continuous hpq)
  (homeomorphism_with_inverse_proper hpq) mu).
Qed.

(** Source for [equivariant_nonzero_forward]: if mu(u) <> 0 for some u
    in K(X), then p#(mu)(u o q) = mu(u) <> 0 with u o q in K(Y),
    supporting "nonzero" in Federer 2.7.2, p. 122. *)
Lemma equivariant_nonzero_forward (mu : (X -> R) -> R) :
  (exists2 u, KX u & mu u <> 0) -> exists2 v, KY v & daniell_pushforward p mu v <> 0.
Proof.
have hqp := homeomorphism_with_inverse_symmetric hpq.
case=> u hu hmu; exists (u \o q).
  exact: (@compactly_supported_compose R Y X q (homeomorphism_continuous hqp)
    (homeomorphism_with_inverse_proper hqp) u hu).
rewrite /daniell_pushforward.
have -> : (u \o q) \o p = u by apply: funext=> x; rewrite /= (homeomorphism_left_inverse hpq).
exact: hmu.
Qed.

(** Source for [equivariant_nonzero_invariant_forward]: p# maps
    nonzero monotone invariant integrals for A to nonzero monotone
    invariant integrals for B, supporting the Haar integrals of Federer
    2.7.2, p. 122, and the relation of p. 123. *)
Lemma equivariant_nonzero_invariant_forward (mu : (X -> R) -> R) :
  is_nonzero_monotone_invariant_integral A mu ->
  is_nonzero_monotone_invariant_integral B (daniell_pushforward p mu).
Proof.
case=> hi hm hn; constructor.
- exact: equivariant_covariant_integral_forward.
- exact: equivariant_monotone_forward.
- exact: equivariant_nonzero_forward.
Qed.

End Equivariant.

Section EquivariantEquivalence.
Variable R : realType.
Variable G : Type.
Variables X Y : topologicalType.
Variables (A : G -> X -> X) (B : G -> Y -> Y) (p : X -> Y) (q : Y -> X).
Hypothesis hpq : is_homeomorphism_with_inverse p q.
Hypothesis hAB : forall g x, p (A g x) = B g (p x).

(** Source for [equivariant_covariant_integral]: Federer 2.7.2,
    p. 123, "mu is a left chi covariant integral if and only if p#(mu)
    is a right chi covariant integral", in the general form for a
    homeomorphism p with p o A_g = B_g o p whenever g in G. The converse
    applies the forward implication to the inverse q, for which
    q o B_g = A_g o q, and uses q#(p#(mu)) = mu. *)
Theorem equivariant_covariant_integral (chi : G -> R) (mu : (X -> R) -> R) :
  is_covariant_integral A chi mu <-> is_covariant_integral B chi (daniell_pushforward p mu).
Proof.
split; first exact: (equivariant_covariant_integral_forward hpq hAB).
move=> h.
have hqp := homeomorphism_with_inverse_symmetric hpq.
have hBA := equivariant_inverse_intertwines hpq hAB.
have := equivariant_covariant_integral_forward hqp hBA h.
by rewrite (equivariant_pushforward_cancel hpq).
Qed.

(** Source for [equivariant_nonzero_invariant_integral]: the
    analogue of the relation of Federer 2.7.2, p. 123, for nonzero
    monotone invariant integrals, used for Haar integrals. Supporting
    theorem, proved like equivariant_covariant_integral. *)
Theorem equivariant_nonzero_invariant_integral (mu : (X -> R) -> R) :
  is_nonzero_monotone_invariant_integral A mu <->
  is_nonzero_monotone_invariant_integral B (daniell_pushforward p mu).
Proof.
split; first exact: (equivariant_nonzero_invariant_forward hpq hAB).
move=> h.
have hqp := homeomorphism_with_inverse_symmetric hpq.
have hBA := equivariant_inverse_intertwines hpq hAB.
have := equivariant_nonzero_invariant_forward hqp hBA h.
by rewrite (equivariant_pushforward_cancel hpq).
Qed.

End EquivariantEquivalence.
