(** Federer (1969), 1.6.3, p. 24. Dimensions are expressed by the size of an
    arbitrary basis of the actual associated subspace. This avoids choosing
    coordinates or a particular finite-dimensional implementation of that
    subspace. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors SimpleCovectors OmegaInjective SubspaceEquality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Dimension.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.

(** Source for [Omega_nonzero_preimage]: Federer 1.6.3, p. 24, use of the
    isomorphism Omega. Supporting lemma: a nonzero covector has a nonzero
    preimage. *)
Lemma Omega_nonzero_preimage m (phi : A_m V K^o m) : phi != 0 ->
  exists xi : exterior_power (Hom V K^o) m,
    xi != 0 /\ phi = Omega_m h2 xi.
Proof.
move=> hphi; have [xi hx] := @Omega_m_finite_surjective K h2 V n e he m phi.
exists xi; split; last exact: esym hx.
apply/eqP=> hz; move: hphi; by rewrite -hx hz linear0 eqxx.
Qed.

(** Source for [covector_basis_exists]: Federer 1.6.3, p. 24, dimension
    bound for the associated subspace. Direct finite-basis formulation:
    there is a basis with at most m members. *)
Theorem covector_basis_exists m (phi : A_m V K^o m) : phi != 0 ->
  exists k (a : 'I_k -> subspace_space (covector_subspace h2 phi)),
    is_basis a /\ (k <= m)%N.
Proof.
move/Omega_nonzero_preimage=> [xi [hx ->]].
rewrite covector_subspace_Omega.
exact: (@associated_basis_exists K h2 (Hom V K^o) m xi hx).
Qed.

(** Source for [covector_basis_bound]: Federer 1.6.3, p. 24, dimension at
    most m. Direct statement for any basis of the associated subspace *)
Theorem covector_basis_bound m (phi : A_m V K^o m) : phi != 0 ->
  forall k (a : 'I_k -> subspace_space (covector_subspace h2 phi)),
    is_basis a -> (k <= m)%N.
Proof.
move/Omega_nonzero_preimage=> [xi [hx ->]].
rewrite covector_subspace_Omega => k a ha.
exact: (@associated_independent_bound K h2 (Hom V K^o) m xi hx k a
  (finite_basis_independent ha)).
Qed.

(** Source for [simple_covector_dimension]: Federer 1.6.3, p. 24, equality
    in the dimension bound for simple covectors. This direction includes
    degree zero. *)
Theorem simple_covector_dimension m (phi : A_m V K^o m) : phi != 0 ->
  simple_covector h2 phi ->
  forall k (a : 'I_k -> subspace_space (covector_subspace h2 phi)),
    is_basis a -> k = m.
Proof.
move/Omega_nonzero_preimage=> [xi [hx ->]].
rewrite simple_covector_Omega covector_subspace_Omega => hs k a ha.
rewrite -(@associated_basis_dimension K h2 (Hom V K^o) m xi hx k a ha).
exact: simple_dimension hs.
Qed.

(** Source for [simple_covector_iff_dimension]: Federer 1.6.3, p. 24,
    equality in the associated dimension bound iff simplicity. Direct
    corrected statement: m must be positive for the reverse implication with
    the literal empty-product convention. This is a local correction, not an
    erratum entry. *)
Theorem simple_covector_iff_dimension m (phi : A_m V K^o m) : phi != 0 ->
  (0 < m)%N ->
  forall k (a : 'I_k -> subspace_space (covector_subspace h2 phi)),
    is_basis a -> (simple_covector h2 phi <-> k = m).
Proof.
move/Omega_nonzero_preimage=> [xi [hx ->]] hm.
rewrite covector_subspace_Omega => k a ha.
rewrite simple_covector_Omega.
rewrite -(@associated_basis_dimension K h2 (Hom V K^o) m xi hx k a ha).
exact: simple_iff_dimension hm.
Qed.

(** Source for [covector_basis_factorisation]: Federer 1.6.3, p. 24,
    covectors behave like vectors under Omega. The equation is in the full
    graded algebra, avoiding subtraction-related degree casts. *)
Theorem covector_basis_factorisation m (phi : A_m V K^o m) : phi != 0 ->
  forall k (a : 'I_k -> subspace_space (covector_subspace h2 phi)),
    is_basis a -> (k <= m)%N /\
    exists psi : A_m V K^o (m-k),
      form_include phi = alternating_wedge h2 (scalar_bilinear K)
        (one_forms_product h2 (scalar_bilinear K) (1 : K^o)
          (fun i => one_form (subspace_val (a i)))) (form_include psi).
Proof.
move/Omega_nonzero_preimage=> [xi [hx ->]].
rewrite covector_subspace_Omega => k a ha.
have [hk [eta ht]] := @associated_basis_factorisation K h2
  (Hom V K^o) m xi hx k a ha.
split=> //; exists (Omega_m h2 eta).
rewrite !Omega_m_include ht Omega_W_wedge.
rewrite -(@Omega_m_include K h2 V k
  (e_lambda (fun i => subspace_val (a i)) (ord_tuple k))) Omega_product.
by rewrite (one_forms_wedge_include h2 (scalar_bilinear K) (@mulr1 K)).
Qed.

(** Source for [simple_covector_basis_product]: Federer 1.6.3, p. 24,
    transfer of the basis-product corollary of 1.6.1. A nonzero simple
    covector is exactly the product of a suitable basis of its associated
    space. This implication remains valid in degree zero. *)
Theorem simple_covector_basis_product m (phi : A_m V K^o m) : phi != 0 ->
  simple_covector h2 phi ->
  exists a : 'I_m -> subspace_space (covector_subspace h2 phi),
    is_basis a /\ phi = one_forms_wedge h2 (scalar_bilinear K) (1 : K^o)
      (fun i => one_form (subspace_val (a i))).
Proof.
move/Omega_nonzero_preimage=> [xi [hx ->]].
rewrite simple_covector_Omega covector_subspace_Omega => hs.
have [a [ha ht]] := @simple_is_basis_product K h2 (Hom V K^o) m xi hx hs.
exists a; split=> //.
have h := congr1 (@Omega_m K h2 V m) ht.
by rewrite Omega_product in h.
Qed.

(** Source for [simple_covector_proportional]: Federer 1.6.3, p. 24,
    transport of the proportionality corollary of 1.6.1. Direct expanded
    statement: two nonzero simple covectors have the same associated space
    iff they are nonzero scalar multiples. *)
Theorem simple_covector_proportional m (phi psi : A_m V K^o m) :
  phi != 0 -> psi != 0 -> simple_covector h2 phi -> simple_covector h2 psi ->
  (covector_subspace h2 phi = covector_subspace h2 psi <->
    exists c : K, c != 0 /\ phi = c *: psi).
Proof.
move/Omega_nonzero_preimage=> [xi [hx ->]].
move/Omega_nonzero_preimage=> [eta [hy ->]].
rewrite !simple_covector_Omega !covector_subspace_Omega => hs ht.
have hp := @simple_associated_equal K h2 (Hom V K^o) m xi eta hx hy ht.
split.
- move=> heq; have heq' v : FedererSimple.T xi v <-> FedererSimple.T eta v.
    by rewrite heq.
  have [c [hc ->]] := proj1 hp heq'.
  exists c; split=> //; exact: linearZ.
- move=> [c [hc hz]]; apply: subspace_ext; apply: (proj2 hp).
  exists c; split=> //; apply: Omega_m_injective; by rewrite linearZ.
Qed.
End Dimension.
