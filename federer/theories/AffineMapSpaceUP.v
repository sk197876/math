(** Federer (1969), 2.7.16, printed pp. 133–134: "The class A(V, V') of all
    affine maps of V into V' is a vectorspace. Using the linear epimorphism
    L: A(V, V') -> Hom(V, V'), L(f)(v) = f(v) - f(0), we construct the
    linear isomorphism M: A(V, V') ~ Hom(V, V') (+) V', M(f) = (L(f),
    f(0))." and "If dim V < oo, then dim A(V, V) < oo". The vector space
    A(V, W) is specified by is_affine_map_space: a vector space A with an
    evaluation ev: A -> (V -> W) which is univalent, carries the vector
    operations of A to the pointwise operations of maps, and whose image is
    the class of all affine maps of AffineMaps.v. This determines A up to a
    unique linear isomorphism compatible with ev. All results below are
    derived from the specification; AffineMapSpaceConstruction.v proves
    existence by the subspace of affine functions and AffineMapSpaceSealed.v
    seals it. Here Hom(V, W) (+) W is the product vector space Hom V W * W.
    The map M is affine_space_iso and its inverse M^{-1}(g, z) = (v |-> z +
    g(v)) is affine_space_iso_inv. If V and W have finite bases of n and k
    members, then A(V, W) has a base of n k + k members, the image under
    M^{-1} of the base of Hom(V, W) (+) W formed by the maps x |-> e_i*(x)
    w_j (1.4.5, p. 21) and the vectors w_j. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import TensorUP Hom LinearBasis BasisSizeTransport ProductFiniteBasis
  HomCompositionDeterminant AffineMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Specification.
Variable R : numFieldType.
Variables V W : lmodType R.

(** Source for [is_affine_map_space]: "The class A(V, V') of all affine
    maps of V into V' is a vectorspace", Federer 2.7.16, p. 133.
    Specification of the vector space A(V, W) through its evaluation
    ev: A -> (V -> W): ev carries the vector operations of A to the
    pointwise operations of maps, ev is univalent, and its image is the
    class of all affine maps of V into W. *)
Record is_affine_map_space (A : lmodType R) (ev : A -> V -> W) : Prop := {
  (** Source for [affine_space_eval_operations]: the vector operations
      of A(V, W) are pointwise, Federer 2.7.16, p. 133. *)
  affine_space_eval_operations : forall (c : R) (f g : A) (v : V), ev (c *: f + g) v = c *: ev f v + ev g v;
  (** Source for [affine_space_eval_inj]: a member of A(V, W) is
      determined by its values, Federer 2.7.16, p. 133. *)
  affine_space_eval_inj : injective ev;
  (** Source for [affine_space_eval_affine]: the members of A(V, W)
      are affine maps, Federer 2.7.16, p. 133. *)
  affine_space_eval_affine : forall f, is_affine_map (ev f);
  (** Source for [affine_space_eval_onto]: every affine map of V into W
      belongs to A(V, W), Federer 2.7.16, p. 133. *)
  affine_space_eval_onto : forall h : V -> W, is_affine_map h -> exists f, ev f = h
}.

Variable A : lmodType R.
Variable ev : A -> V -> W.
Hypothesis hA : is_affine_map_space ev.

(** Source for [affine_space_evalD]: (f + g)(v) = f(v) + g(v) in
    A(V, W), Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_space_evalD (f g : A) (v : V) : ev (f + g) v = ev f v + ev g v.
Proof. by have := affine_space_eval_operations hA 1 f g v; rewrite !scale1r. Qed.

(** Source for [affine_space_eval0]: the zero of A(V, W) is the zero
    map, Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_space_eval0 (v : V) : ev 0 v = 0.
Proof.
have h := affine_space_evalD 0 0 v; rewrite addr0 in h.
by move: (congr1 (fun x => x - ev 0 v) h); rewrite /= subrr addrK=> <-.
Qed.

(** Source for [affine_space_evalZ]: (c f)(v) = c f(v) in A(V, W),
    Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_space_evalZ (c : R) (f : A) (v : V) : ev (c *: f) v = c *: ev f v.
Proof. by rewrite -[c *: f]addr0 (affine_space_eval_operations hA) affine_space_eval0 addr0. Qed.

(** Source for [affine_space_evalN]: (-f)(v) = -f(v) in A(V, W),
    Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_space_evalN (f : A) (v : V) : ev (- f) v = - ev f v.
Proof. by rewrite -scaleN1r affine_space_evalZ scaleN1r. Qed.

(** Source for [affine_space_evalB]: (f - g)(v) = f(v) - g(v) in
    A(V, W), Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_space_evalB (f g : A) (v : V) : ev (f - g) v = ev f v - ev g v.
Proof. by rewrite affine_space_evalD affine_space_evalN. Qed.

(** Source for [affine_space_hom]: "the linear epimorphism
    L: A(V, V') -> Hom(V, V'), L(f)(v) = f(v) - f(0)", Federer 2.7.16,
    p. 133: L(f) as a member of Hom(V, W). Definition. *)
Definition affine_space_hom (f : A) : Hom V W :=
  @HomMap R V W (affine_linear_part (ev f))
    (introT (asboolP _) (affine_linear_part_linear (affine_space_eval_affine hA f))).

(** Source for [affine_space_homE]: L(f)(v) = f(v) - f(0), Federer
    2.7.16, p. 133. Supporting lemma. *)
Lemma affine_space_homE (f : A) (v : V) : affine_space_hom f v = ev f v - ev f 0.
Proof. by []. Qed.

(** Source for [affine_space_decomposition]: f(v) = f(0) + L(f)(v),
    Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_space_decomposition (f : A) (v : V) : ev f v = ev f 0 + affine_space_hom f v.
Proof. by rewrite affine_space_homE addrC subrK. Qed.

(** Source for [affine_space_iso]: "M(f) = (L(f), f(0))", Federer
    2.7.16, p. 133, with values in the product space Hom(V, W) x W.
    Definition. *)
Definition affine_space_iso (f : A) : (Hom V W * W)%type := (affine_space_hom f, ev f 0).

(** Source for [affine_space_iso_linear]: M is linear, Federer 2.7.16,
    p. 133, "the linear isomorphism M". Direct formalisation of the
    linearity. *)
Lemma affine_space_iso_linear : linear affine_space_iso.
Proof.
move=> c f g; congr pair; last by rewrite (affine_space_eval_operations hA).
apply: hom_ext=> v; rewrite hom_addE hom_scaleE !affine_space_homE.
rewrite !(affine_space_eval_operations hA) scalerBr opprD addrACA.
by [].
Qed.

HB.instance Definition _ := GRing.isLinear.Build R A (Hom V W * W)%type *:%R affine_space_iso
  affine_space_iso_linear.

(** Source for [affine_space_iso_fun_affine]: the map v |-> z + g(v) is
    affine for linear g, Federer 2.7.16, p. 134, "M^{-1}(g, z) =
    tau_z o g". Supporting lemma. *)
Lemma affine_space_iso_fun_affine (p : (Hom V W * W)%type) : is_affine_map (fun v => p.2 + p.1 v).
Proof. by have [h _ _ _] := affine_isomorphism (hom_as_linear p.1) p.2. Qed.

(** Source for [affine_space_iso_inv]: the inverse M^{-1}(g, z) of M,
    the member of A(V, W) with values z + g(v), Federer 2.7.16,
    pp. 133–134. Definition by the specification. *)
Definition affine_space_iso_inv (p : (Hom V W * W)%type) : A :=
  projT1 (cid (affine_space_eval_onto hA (affine_space_iso_fun_affine p))).

(** Source for [affine_space_iso_invE]: M^{-1}(g, z)(v) = z + g(v),
    Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma affine_space_iso_invE (p : (Hom V W * W)%type) : ev (affine_space_iso_inv p) = fun v => p.2 + p.1 v.
Proof. by rewrite /affine_space_iso_inv; case: cid. Qed.

(** Source for [affine_space_isoK]: M^{-1}(M(f)) = f, Federer 2.7.16,
    p. 133: f(v) = f(0) + L(f)(v). Supporting lemma. *)
Lemma affine_space_isoK : cancel affine_space_iso affine_space_iso_inv.
Proof.
move=> f; apply: (affine_space_eval_inj hA); rewrite affine_space_iso_invE /=.
by apply: funext=> v; rewrite -affine_space_decomposition.
Qed.

(** Source for [affine_space_iso_invK]: M(M^{-1}(g, z)) = (g, z),
    Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_space_iso_invK : cancel affine_space_iso_inv affine_space_iso.
Proof.
move=> [g z]; rewrite /affine_space_iso affine_space_iso_invE /=.
have hg0 : g 0 = 0 by exact: (linear0 (hom_as_linear g)).
congr pair; last by rewrite hg0 addr0.
by apply: hom_ext=> v; rewrite affine_space_homE affine_space_iso_invE /= hg0 addr0 addrC addKr.
Qed.

(** Source for [affine_space_iso_bijective]: "the linear isomorphism
    M: A(V, V') ~ Hom(V, V') (+) V'", Federer 2.7.16, p. 133: M is
    bijective. Direct formalisation; linearity is
    [affine_space_iso_linear]. *)
Theorem affine_space_iso_bijective : bijective affine_space_iso.
Proof. by exists affine_space_iso_inv; [exact: affine_space_isoK|exact: affine_space_iso_invK]. Qed.

(** Source for [affine_space_iso_inv_linear]: M^{-1} is linear,
    Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_space_iso_inv_linear : linear affine_space_iso_inv.
Proof.
move=> c p q; apply: (can_inj affine_space_isoK).
by rewrite affine_space_iso_invK (affine_space_iso_linear c) !affine_space_iso_invK.
Qed.

HB.instance Definition _ := GRing.isLinear.Build R (Hom V W * W)%type A *:%R affine_space_iso_inv
  affine_space_iso_inv_linear.

(** Source for [affine_space_hom_onto]: "the linear epimorphism L",
    Federer 2.7.16, p. 133: L(M^{-1}(g, z)) = g, so L maps onto
    Hom(V, W). Supporting lemma. *)
Lemma affine_space_hom_onto (g : Hom V W) (z : W) : affine_space_hom (affine_space_iso_inv (g, z)) = g.
Proof. by have := affine_space_iso_invK (g, z); rewrite /affine_space_iso=> -[]. Qed.

(** Source for [affine_space_iso_inv_zero]: M^{-1}(g, z)(0) = z,
    Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_space_iso_inv_zero (g : Hom V W) (z : W) : ev (affine_space_iso_inv (g, z)) 0 = z.
Proof. by have := affine_space_iso_invK (g, z); rewrite /affine_space_iso=> -[]. Qed.

Variables n k : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable c : 'I_k -> W.
Hypothesis hc : is_basis c.

(** Source for [affine_space_basis]: a base of A(V, W): the image under
    M^{-1} of the base of Hom(V, W) x W formed by the pairs
    (x |-> e_i*(x) w_j, 0) and (0, w_j), Federer 2.7.16, p. 134, "dim
    A(V, V) < oo", with 1.4.5, p. 21, and 1.7.11, p. 36. Definition. *)
Definition affine_space_basis : 'I_(#|{: 'I_n * 'I_k}| + k) -> A :=
  fun i => affine_space_iso_inv (cartesian_basis (hom_rank_one_base hb c) c i).

(** Source for [affine_space_basisP]: affine_space_basis is a base of
    A(V, W), Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma affine_space_basisP : is_basis affine_space_basis.
Proof.
apply: (@basis_transport R _ (Hom V W * W)%type A _
  (GRing.Linear.clone _ _ _ _ affine_space_iso_inv _) (GRing.Linear.clone _ _ _ _ affine_space_iso _)).
- exact: affine_space_iso_invK.
- exact: affine_space_isoK.
- exact: cartesian_basisP (hom_rank_one_baseP hb hc) hc.
Qed.

(** Source for [affine_space_finite_dimensional]: "If dim V < oo, then
    dim A(V, V) < oo", Federer 2.7.16, p. 134, for A(V, W) with
    dim V = n and dim W = k: A(V, W) has a base of n k + k members.
    Direct formalisation, with the dimension. *)
Theorem affine_space_finite_dimensional : exists u : 'I_(n * k + k) -> A, is_basis u.
Proof.
have hcard : #|{: 'I_n * 'I_k}| + k = n * k + k by rewrite card_prod !card_ord.
by exists (fun i => affine_space_basis (cast_ord (esym hcard) i)); exact: basis_cast_size affine_space_basisP.
Qed.

End Specification.

Section Uniqueness.
Variable R : numFieldType.
Variables V W : lmodType R.

(** Source for [affine_map_space_unique]: A(V, W) is determined by its
    specification, Federer 2.7.16, p. 133: if (A, ev) and (A', ev') both
    satisfy it, the map f |-> the member of A' with the values of f is a
    linear bijection compatible with the evaluations. Supporting lemma
    justifying the definite article. *)
Lemma affine_map_space_unique (A A' : lmodType R) (ev : A -> V -> W) (ev' : A' -> V -> W) :
  is_affine_map_space ev -> is_affine_map_space ev' ->
  exists phi : A -> A', [/\ linear phi, bijective phi & forall f, ev' (phi f) = ev f].
Proof.
move=> hA hA'.
pose phi (f : A) : A' := projT1 (cid (affine_space_eval_onto hA' (affine_space_eval_affine hA f))).
have hphi f : ev' (phi f) = ev f by rewrite /phi; case: cid.
pose psi (f : A') : A := projT1 (cid (affine_space_eval_onto hA (affine_space_eval_affine hA' f))).
have hpsi f : ev (psi f) = ev' f by rewrite /psi; case: cid.
exists phi; split=> //.
- move=> a f g; apply: (affine_space_eval_inj hA'); apply: funext=> v.
  by rewrite hphi !(affine_space_eval_operations hA', affine_space_eval_operations hA) !hphi.
- exists psi=> f.
  + by apply: (affine_space_eval_inj hA); rewrite hpsi hphi.
  + by apply: (affine_space_eval_inj hA'); rewrite hphi hpsi.
Qed.

End Uniqueness.
