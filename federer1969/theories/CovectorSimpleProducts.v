(** Federer (1969), 1.6.3, pp. 24-25, transport of simple-vector properties
    to covectors. Products and disjointness are proved through Omega. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import SimpleVectors SimpleCovectors SubspaceEquality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Products.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.

(** Source for [Omega_m_wedge]: Federer 1.6.3, p. 24, use of the
    algebra isomorphism of 1.4.4. Supporting component identity:
    Omega carries exterior products to alternating products. *)
Lemma Omega_m_wedge p q (xi : exterior_power (Hom V K^o) p)
  (eta : exterior_power (Hom V K^o) q) :
  Omega_m h2 (exterior_product xi eta) =
    form_wedge h2 (scalar_bilinear K) (Omega_m h2 xi) (Omega_m h2 eta).
Proof.
apply: (can_inj (@form_includeK K V K^o (p+q))).
rewrite form_wedge_include !Omega_m_include exterior_productE.
exact: (@Omega_W_wedge K h2 V (scalar_algebra K) (@mulrC K)).
Qed.

(** Source for [Omega_m_nonzero]: Federer 1.6.3, p. 24,
    transport through Omega. Supporting consequence of injectivity:
    a covector in its image vanishes iff its preimage does. *)
Lemma Omega_m_nonzero m (xi : exterior_power (Hom V K^o) m) :
  (Omega_m h2 xi != 0) = (xi != 0).
Proof.
have h := inj_eq (@Omega_m_injective K h2 V m) xi 0.
rewrite linear0 in h; by rewrite h.
Qed.

(** Source for [simple_covector_preimage]: Federer 1.6.3, p. 24,
    transport of simple covectors. Supporting existence statement:
    every simple covector has a simple preimage under Omega, even
    without a finite-dimensional hypothesis. *)
Lemma simple_covector_preimage m (phi : A_m V K^o m) :
  simple_covector h2 phi -> exists xi : exterior_power (Hom V K^o) m,
    simple xi /\ phi = Omega_m h2 xi.
Proof.
move=> [a ->]; exists (e_lambda (fun i => one_hom (a i)) (ord_tuple m)).
split; first exact: product_simple.
rewrite Omega_product.
have he : (fun i => one_form (one_hom (a i))) = a.
  by apply: funext => i; rewrite one_homK.
by rewrite he.
Qed.

(** Source for [simple_exterior_product]: Federer 1.6.3, p. 24,
    transport of the simple-vector product property. Supporting
    observation: concatenating decompositions gives a decomposition
    of the exterior product, including degree zero. *)
Lemma simple_exterior_product (U : lmodType K) p q
  (xi : exterior_power U p) (eta : exterior_power U q) :
  simple xi -> simple eta -> simple (exterior_product xi eta).
Proof.
move=> [t ->] [s ->]; rewrite !tuple_product concatenated_product.
exact: product_simple.
Qed.

(** Source for [simple_covector_product]: Federer 1.6.3, pp. 24-25,
    alternating products of simple covectors. Supporting closure
    statement used in the intersection corollary. *)
Theorem simple_covector_product p q (phi : A_m V K^o p) (psi : A_m V K^o q) :
  simple_covector h2 phi -> simple_covector h2 psi ->
    simple_covector h2 (form_wedge h2 (scalar_bilinear K) phi psi).
Proof.
move/simple_covector_preimage=> [xi [hx ->]].
move/simple_covector_preimage=> [eta [hy ->]].
rewrite -Omega_m_wedge simple_covector_Omega; exact: simple_exterior_product hx hy.
Qed.

(** Source for [product_word_nonzero]: Federer 1.6.3, pp. 24-25,
    nonzero products. Supporting bridge between a homogeneous product
    and its representative in the full exterior algebra. *)
Lemma product_word_nonzero (U : lmodType K) m (e : 'I_m -> U) :
  e_lambda e (ord_tuple m) != 0 ->
    exterior_word [seq e i | i <- enum 'I_m] != 0.
Proof.
move=> hx; apply/eqP=> hz; apply: (elimT negP hx); apply/eqP; apply: val_inj.
change (component_val (e_lambda e (ord_tuple m)) = component_val (0 : exterior_power U m)).
by rewrite e_lambdaE linear0.
Qed.

(** Source for [simple_exterior_product_disjoint]: Federer 1.6.3,
    p. 25, reference to the simple-product direct-sum property of 1.6.1.
    Supporting equivalence: the product of nonzero simple vectors is
    nonzero iff their associated spaces meet only at zero. *)
Theorem simple_exterior_product_disjoint (U : lmodType K) p q
  (xi : exterior_power U p) (eta : exterior_power U q) :
  xi != 0 -> eta != 0 -> simple xi -> simple eta ->
  (exterior_product xi eta != 0 <->
    forall v, FedererSimple.T xi v -> FedererSimple.T eta v -> v=0).
Proof.
move=> hx hy hs ht; split.
- move=> hz; exact: (proj2 (proj1 (@simple_product_direct_sum K h2 U p q xi eta hx hy hs ht) hz)).
- move=> hd; move: hs ht hx hy hd => [t ->] [s ->].
  rewrite !tuple_product => hx hy hd; rewrite concatenated_product.
  apply: (@independent_product_nonzero K h2 U (p+q)).
  apply: disjoint_concatenation_independent
    (nonzero_word_independent (product_word_nonzero hx))
    (nonzero_word_independent (product_word_nonzero hy)) _ => v hv hw.
  apply: hd.
  + exact: (proj2 (@product_associated_space K h2 U p (tnth t) hx v) hv).
  + exact: (proj2 (@product_associated_space K h2 U q (tnth s) hy v) hw).
Qed.

(** Source for [simple_covector_product_disjoint]: Federer 1.6.3, p. 25,
    nonzero product in the intersection corollary. *)
Theorem simple_covector_product_disjoint p q (phi : A_m V K^o p) (psi : A_m V K^o q) :
  phi != 0 -> psi != 0 -> simple_covector h2 phi -> simple_covector h2 psi ->
  (form_wedge h2 (scalar_bilinear K) phi psi != 0 <->
    forall a, covector_subspace h2 phi a -> covector_subspace h2 psi a -> a=0).
Proof.
move=> hp hq /simple_covector_preimage [xi [hx hphi]] /simple_covector_preimage [eta [hy hpsi]].
move: hp hq; rewrite hphi hpsi !Omega_m_nonzero => hp hq.
rewrite -Omega_m_wedge Omega_m_nonzero !covector_subspace_Omega.
exact: simple_exterior_product_disjoint hp hq hx hy.
Qed.

(** Source for [simple_covector_product_space]: Federer 1.6.3, p. 25,
    associated space of the nonzero product in the corollary. Expanded
    supporting statement: that space is the sum of the two associated
    spaces. *)
Theorem simple_covector_product_space p q (phi : A_m V K^o p) (psi : A_m V K^o q) :
  phi != 0 -> psi != 0 -> simple_covector h2 phi -> simple_covector h2 psi ->
  form_wedge h2 (scalar_bilinear K) phi psi != 0 -> forall a,
  covector_subspace h2 (form_wedge h2 (scalar_bilinear K) phi psi) a <->
    exists b c, covector_subspace h2 phi b /\ covector_subspace h2 psi c /\ a=b+c.
Proof.
move=> hp hq /simple_covector_preimage [xi [hx hphi]] /simple_covector_preimage [eta [hy hpsi]].
move: hp hq; rewrite hphi hpsi !Omega_m_nonzero => hp hq.
rewrite -Omega_m_wedge Omega_m_nonzero !covector_subspace_Omega => hz a.
exact: (proj1 (proj1 (@simple_product_direct_sum K h2 (Hom V K^o)
  p q xi eta hp hq hx hy) hz) a).
Qed.
End Products.
