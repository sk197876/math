(** Federer (1969), 1.6.3, p. 25, dimension argument in the intersection
    corollary. We express dimensions by the cardinalities of arbitrary
    bases. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors SimpleCovectors CovectorDimension
  SimpleAdaptedBasis DualitySimplicity DualityAnnihilator Annihilator
  SubspaceBasisProduct SubspaceEquality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CanonicalDual.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation omega := (fun i => one_form (dual_basis he i)).
Local Notation ot := (omega_lambda h2 omega (Lambda_top n)).

(** Source for [canonical_top_covector_nonzero]: Federer 1.6.3,
    p. 25, reference to the duality isomorphisms of 1.5.2. Supporting
    fact: the product of the dual basis covectors is nonzero. *)
Lemma canonical_top_covector_nonzero : ot != 0.
Proof.
exact: basis_vector_nonzero (@omega_lambda_basis K h2 V n n e omega he
  (@finite_dual_biorthogonal K V n e he)) (Lambda_top n).
Qed.

(** Source for [canonical_D_p_nonzero]: Federer 1.6.3, p. 25,
    duality isomorphism. Supporting consequence of the inverse identity:
    a nonzero vector has a nonzero dual covector. *)
Lemma canonical_D_p_nonzero p (hp : (p <= n)%N) (xi : exterior_power V p) :
  xi != 0 -> D_p ot hp xi != 0.
Proof.
move=> hx; apply/eqP=> hz; apply: (elimT negP hx); apply/eqP.
apply: (can_inj (@D_pK K h2 V n e omega he
  (@finite_dual_biorthogonal K V n e he) p hp)).
by rewrite linear0.
Qed.

(** Source for [dual_associated_basis_size]: Federer 1.6.3, p. 25,
    annihilator dimension used in the corollary. Supporting statement:
    the space associated with D_p xi has dimension n-p for every
    nonzero simple xi, including the zero-output-degree endpoint. *)
Lemma dual_associated_basis_size p (hp : (p <= n)%N) (xi : exterior_power V p) :
  xi != 0 -> simple xi ->
  forall k (a : 'I_k -> subspace_space (covector_subspace h2 (D_p ot hp xi))),
    is_basis a -> k = (n-p)%N.
Proof.
move=> hx hs k a ha.
have hd := canonical_D_p_nonzero hp hx.
have [hz|hz] := eqVneq (n-p)%N 0%N.
- have hk := @covector_basis_bound K h2 V n e he (n-p) (D_p ot hp xi) hd k a ha.
  move: hk; rewrite hz leqn0 => /eqP hk; by rewrite hk.
- have hpn : (p < n)%N by move: hz; rewrite -lt0n subn_gt0.
  have hsimple := @D_p_simple_nonzero K h2 V n e he ot p hp xi hpn hx hs.
  exact: (@simple_covector_dimension K h2 V n e he (n-p) (D_p ot hp xi)
    hd hsimple k a ha).
Qed.

(** Source for [annihilator_simple_basis_exists]: Federer 1.6.3,
    p. 25, dimension of the annihilator of a p-dimensional associated
    space. Direct basis formulation: its annihilator has a basis with
    n-p members. Endpoint degrees require no simplicity convention. *)
Theorem annihilator_simple_basis_exists p (hp : (p <= n)%N)
  (xi : exterior_power V p) : xi != 0 -> simple xi ->
  exists a : 'I_(n-p) -> subspace_space (annihilator (FedererSimple.T xi)),
    is_basis a.
Proof.
move=> hx hs.
have ht := @D_p_associated_annihilator K h2 V n e he ot p hp xi
  canonical_top_covector_nonzero hx hs.
have hd := canonical_D_p_nonzero hp hx.
have [k [a [ha hk]]] := @covector_basis_exists K h2 V n e he (n-p) (D_p ot hp xi) hd.
have hsize : k = (n-p)%N := @dual_associated_basis_size p hp xi hx hs k a ha.
rewrite -ht.
exists (fun i => a (cast_ord (esym hsize) i)).
exact: (@basis_cast_size K (subspace_space (covector_subspace h2 (D_p ot hp xi)))
  k (n-p) hsize a ha).
Qed.
End CanonicalDual.

(** Source for [finite_subspace_basis_exists]: Federer 1.6.3,
    p. 25, dimensions of intersections and annihilators. Supporting
    existence theorem: a subspace of an n-dimensional space has a
    finite basis of size at most n. *)
Theorem finite_subspace_basis_exists (K : fieldType) (V : lmodType K)
  n (e : 'I_n -> V) (he : is_basis e) (S : subspace V) :
  exists k (a : 'I_k -> subspace_space S), is_basis a /\ (k <= n)%N.
Proof.
apply: (@bounded_independent_basis K (subspace_space S) n) => k a ha.
have hi := finite_independent_map (@subspace_val_injective K V S) ha.
have hd := @finite_independent_dimension K (finite_basis_vect he) k
  (fun i => subspace_val (a i)) hi.
by rewrite finite_basis_dimension card_ord in hd.
Qed.

(** Source for [annihilator_basis_exists]: Federer 1.6.3, p. 25,
    dimension argument in the intersection corollary. Supporting general
    form: if S has a k-member basis in an n-dimensional space, its
    annihilator has an (n-k)-member basis. *)
Theorem annihilator_basis_exists (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
  (S : subspace V) k (a : 'I_k -> subspace_space S) (ha : is_basis a) :
  (k <= n)%N /\ exists b : 'I_(n-k) -> subspace_space (annihilator S), is_basis b.
Proof.
have hi := finite_independent_map (@subspace_val_injective K V S)
  (finite_basis_independent ha).
have hk := @finite_independent_dimension K (finite_basis_vect he) k
  (fun i => subspace_val (a i)) hi.
rewrite finite_basis_dimension card_ord in hk; split=> //.
pose xi := subspace_basis_product a.
have hx := subspace_basis_product_nonzero h2 ha.
have hs : simple xi := subspace_basis_product_simple a.
have ht : FedererSimple.T xi = S.
  apply: subspace_ext => v.
  exact: (@subspace_basis_product_associated K h2 V S k a ha v).
rewrite -ht.
exact: (@annihilator_simple_basis_exists K h2 V n e he k hk xi hx hs).
Qed.
