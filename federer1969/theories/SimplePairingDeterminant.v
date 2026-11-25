(** Federer (1969), 1.6.4, p. 25, complete pairing/determinant statement and
    proof. The endomorphism acts on the actual associated subspace. The
    ambient space need not be finite dimensional; the associated space has
    the product factors as a basis. Empty products are included. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import SimpleVectors CovectorProductNaturality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section BasisCalculation.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable m : nat.
Variable e : 'I_m -> V.
Hypothesis he : is_basis e.
Variable alpha : 'I_m -> A_m V K^o 1.
Variable f : {linear V -> V}.
Hypothesis hf : forall i, f (e i) = \sum_j (alpha j [tuple e i] : K) *: e j.
Local Notation omega := (fun i => one_form (dual_basis he i)).

(** Source for [pairing_endomorphism_dual_basis]: Federer 1.6.4, p. 25,
    first identity in the proof after choosing the dual basis. Direct
    assertion: the pullback of the j-th dual basis one-form by f is alpha_j. *)
Lemma pairing_endomorphism_dual_basis j : A_m_dual f (omega j) = alpha j.
Proof.
apply: one_hom_injective; apply: hom_ext => v.
apply: (basis_linear_ext he (hom_as_linear (one_hom (A_m_dual f (omega j))))
  (hom_as_linear (one_hom (alpha j)))) v => i.
change (one_hom (A_m_dual f (omega j)) (e i) = one_hom (alpha j) (e i)).
rewrite !one_homE A_m_dualE.
change (one_form (dual_basis he j) [tuple f (e i)] = alpha j [tuple e i]).
rewrite one_formE hf.
apply: (@biorthogonal_sum K V 'I_m (dual_basis he) e) => a b.
by rewrite dual_basisE eq_sym.
Qed.

(** Source for [pairing_top_form_pullback]: Federer 1.6.4, p. 25, displayed
    proof identity. Direct assertion: the product of the alpha_j is the
    pullback of the dual top form, hence its determinant multiple. *)
Lemma pairing_top_form_pullback :
  one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) alpha =
    A_m_dual f (omega_lambda h2 omega (Lambda_top m)).
Proof.
rewrite omega_lambda_top_product one_forms_wedge_natural.
have h : (fun i => A_m_dual f (omega i)) = alpha.
  by apply: funext => i; exact: pairing_endomorphism_dual_basis.
by rewrite h.
Qed.

(** Source for [basis_pairing_determinant]: Federer 1.6.4, p. 25,
    final displayed proof identity after reduction to a basis of the
    whole space. Direct assertion: the pairing of the basis product
    with the product of the alpha_j is det(f). *)
Theorem basis_pairing_determinant :
  pairing (e_lambda e (ord_tuple m))
    (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) alpha) = det h2 he f.
Proof.
rewrite pairing_top_form_pullback (A_m_dual_det h2 he)
  (bilZr (@pairing_bilinear K V K^o m)).
change (det h2 he f * pairing (e_lambda e (val (Lambda_top m)))
  (omega_lambda h2 omega (Lambda_top m)) = det h2 he f).
by rewrite (pairing_e_omega h2 (@finite_dual_biorthogonal K V m e he)) eqxx mulr1.
Qed.
End BasisCalculation.

Section AssociatedEndomorphism.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable m : nat.
Variable e : 'I_m -> V.
Variable alpha : 'I_m -> A_m V K^o 1.
Local Notation xi := (e_lambda e (ord_tuple m)).
Local Notation T := (FedererSimple.T xi).
Local Notation U := (GRing.Lmodule.clone K (subspace_space T) _).
Local Notation b := (product_basis e).

(** Source for [is_pairing_endomorphism]: Federer 1.6.4, p. 25,
    displayed characterisation of f. Direct abstract specification:
    on the i-th product factor, f has coordinates given by pairing
    that factor with alpha_j. The vectors lie in the actual carrier T. *)
Definition is_pairing_endomorphism (f : {linear U -> U}) :=
  forall i, f (b i) = \sum_j (alpha j [tuple e i] : K) *: b j.

(** Source for [pairing_endomorphism_unique]: Federer 1.6.4, p. 25,
    endomorphism characterised by its values on the factors. Supporting
    uniqueness proof: the nonzero product makes those factors a basis
    of T, so its characteristic equations determine f on every vector. *)
Lemma pairing_endomorphism_unique (hxi : xi != 0) (f g : {linear U -> U}) :
  is_pairing_endomorphism f -> is_pairing_endomorphism g -> f =1 g.
Proof.
move=> hf hg; apply: (basis_linear_ext (@product_basisP K h2 V m e hxi) f g) => i.
by rewrite hf hg.
Qed.

(** Source for [pairing_endomorphism_apply]: Federer 1.6.4, p. 25,
    characterisation of f. Existence construction: the sum of alpha_j
    evaluated on the included vector, multiplied by the j-th basis
    vector of the associated space. *)
Definition pairing_endomorphism_apply (v : U) : U :=
  \sum_j (one_hom (alpha j) (subspace_val v) : K) *: b j.

(** Source for [pairing_endomorphism_linear]: Federer 1.6.4, p. 25,
    endomorphism f. Supporting verification that the existence
    construction is a linear map on T. *)
Lemma pairing_endomorphism_linear : linear pairing_endomorphism_apply.
Proof.
move=> c x y; rewrite /pairing_endomorphism_apply scaler_sumr -big_split.
apply: eq_bigr => j _.
rewrite (@subspace_val_linear K V T c x y)
  (hom_linear (one_hom (alpha j))) scalerDl scalerA.
by [].
Qed.
HB.instance Definition _ := GRing.isLinear.Build K U U *:%R
  pairing_endomorphism_apply pairing_endomorphism_linear.

(** Source for [pairing_endomorphism]: Federer 1.6.4, p. 25,
    endomorphism f. Packages the construction with its proved linearity. *)
Definition pairing_endomorphism : {linear U -> U} :=
  GRing.Linear.clone _ _ _ _ pairing_endomorphism_apply _.

(** Source for [pairing_endomorphism_characteristic]: Federer 1.6.4,
    p. 25, displayed characterisation. Supporting verification that
    the constructed endomorphism satisfies the prescribed equations. *)
Lemma pairing_endomorphism_characteristic : is_pairing_endomorphism pairing_endomorphism.
Proof.
move=> i; rewrite /pairing_endomorphism /pairing_endomorphism_apply.
apply: eq_bigr => j _; by rewrite product_basisE one_homE.
Qed.

(** Source for [pairing_endomorphism_exists]: Federer 1.6.4, p. 25,
    the endomorphism f characterised by the displayed equations.
    Direct existence-and-uniqueness theorem on the actual associated
    space. Uniqueness is pointwise equality of linear maps. *)
Theorem pairing_endomorphism_exists (hxi : xi != 0) :
  exists f : {linear U -> U}, is_pairing_endomorphism f /\
    forall g, is_pairing_endomorphism g -> g =1 f.
Proof.
exists pairing_endomorphism; split; first exact: pairing_endomorphism_characteristic.
move=> g hg; exact: (@pairing_endomorphism_unique hxi g pairing_endomorphism hg
  pairing_endomorphism_characteristic).
Qed.

(** Source for [associated_product_natural]: Federer 1.6.4, p. 25,
    reduction by naturality. Supporting identity: the basis product
    in T maps to the original product in V under the induced inclusion. *)
Lemma associated_product_natural :
  exterior_power_map (subspace_inclusion T) m (e_lambda b (ord_tuple m)) = xi.
Proof.
rewrite exterior_basis_product_natural.
have hb : (fun i => subspace_inclusion T (b i)) = e by apply: funext => i.
by rewrite hb.
Qed.

(** Source for [simple_pairing_determinant_characteristic]: Federer
    1.6.4, p. 25, main assertion. Direct formalisation for any linear
    endomorphism satisfying the printed characterisation; the determinant
    is taken on the actual associated space with its factor basis. *)
Theorem simple_pairing_determinant_characteristic (hxi : xi != 0)
  (f : {linear U -> U}) : is_pairing_endomorphism f ->
  pairing xi (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) alpha) =
    det h2 (@product_basisP K h2 V m e hxi) f.
Proof.
move=> hf.
pose a i := A_m_dual (subspace_inclusion T) (alpha i).
have hfa i : f (b i) = \sum_j (a j [tuple b i] : K) *: b j.
  rewrite hf; apply: eq_bigr => j _; rewrite /a A_m_dualE.
  have ht : map_tuple (subspace_inclusion T) [tuple b i] = [tuple e i].
    by apply: val_inj.
  by rewrite ht.
have hn := A_m_dual_pairing (subspace_inclusion T)
  (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) alpha)
  (e_lambda b (ord_tuple m)).
rewrite associated_product_natural one_forms_wedge_natural in hn.
rewrite -hn.
exact: (@basis_pairing_determinant K h2 U m b (@product_basisP K h2 V m e hxi) a f hfa).
Qed.

(** Source for [simple_pairing_determinant]: Federer 1.6.4, p. 25,
    main assertion. Direct theorem with the now-proved unique
    endomorphism supplied by the existence construction. It includes
    the empty product, for which the determinant is one. *)
Theorem simple_pairing_determinant (hxi : xi != 0) :
  pairing xi (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) alpha) =
    det h2 (@product_basisP K h2 V m e hxi) pairing_endomorphism.
Proof. exact: simple_pairing_determinant_characteristic pairing_endomorphism_characteristic. Qed.
End AssociatedEndomorphism.
