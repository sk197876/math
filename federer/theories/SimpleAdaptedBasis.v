(** Federer (1969), 1.6.3, pp. 24-25, adapted-basis proof of the duality
    assertions. The algebraic statements below hold over fields of
    characteristic different from two. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import SimpleVectors SimpleCovectors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [indexed_productE]: Federer 1.6.3, pp. 24-25,
    products in an adapted basis. Supporting change of indexing from
    an ordered tuple to an ordinal family; the product is unchanged. *)
Lemma indexed_productE (K : fieldType) (I : choiceType) (V : lmodType K)
  (e : I -> V) m (t : m.-tuple I) :
  e_lambda e t = e_lambda (fun i => e (tnth t i)) (ord_tuple m).
Proof.
apply: val_inj.
change (component_val (e_lambda e t) =
  component_val (e_lambda (fun i => e (tnth t i)) (ord_tuple m))).
rewrite !e_lambdaE; congr (exterior_word _).
change (map e t = map (fun i => e (tnth t i)) (enum 'I_m)).
by rewrite (map_comp e (tnth t)) map_tnth_enum.
Qed.

(** Source for [indexed_product_simple]: Federer 1.6.3, p. 25,
    adapted-basis products. Supporting observation: every product
    indexed by a tuple is simple, including the empty product. *)
Lemma indexed_product_simple (K : fieldType) (I : choiceType) (V : lmodType K)
  (e : I -> V) m (t : m.-tuple I) : simple (e_lambda e t).
Proof. rewrite indexed_productE; exact: product_simple. Qed.

(** Source for [indexed_product_associated]: Federer 1.6.3, p. 25,
    associated space in a basis. Supporting instance of 1.6.1:
    a nonzero product has the span of its factors as associated space. *)
Lemma indexed_product_associated (K : fieldType) (h2 : (1+1 : K) != 0)
  (I : choiceType) (V : lmodType K) (e : I -> V) m (t : m.-tuple I) :
  e_lambda e t != 0 -> forall v,
    FedererSimple.T (e_lambda e t) v <-> in_finite_span (fun i => e (tnth t i)) v.
Proof.
rewrite indexed_productE => hx v.
exact: (@product_associated_space K h2 V m (fun i => e (tnth t i)) hx v).
Qed.

(** Source for [finite_basis_extension_fixed]: Federer 1.6.3, p. 25, adapted
    dual bases; supporting linear algebra: an independent p-family extends
    to a basis indexed by the given dimension n. *)
Theorem finite_basis_extension_fixed (K : fieldType) (V : lmodType K)
  p n (a : 'I_p -> V) (e : 'I_n -> V) (hp : (p <= n)%N) :
  finite_independent a -> is_basis e ->
  exists b : 'I_n -> V, is_basis b /\
    forall i, b (widen_ord hp i) = a i.
Proof.
move=> ha he.
have [l [hpl [b [hb hba]]]] := finite_basis_extension ha he.
have hl : l = n := finite_basis_size hb he.
subst l; exists b; split=> // i.
have hi : widen_ord hp i = widen_ord hpl i by apply: val_inj.
by rewrite hi hba.
Qed.

(** Source for [initial_productE]: Federer 1.6.3, p. 25, product of
    the first p basis vectors. Supporting index identity relating this
    product to the general ordered-index notation of 1.3.1. *)
Lemma initial_productE (K : fieldType) (V : lmodType K) p n
  (hp : (p <= n)%N) (b : 'I_n -> V) :
  e_lambda b (val (Lambda_initial hp)) =
    e_lambda (fun i => b (widen_ord hp i)) (ord_tuple p).
Proof.
apply: val_inj.
change (component_val (e_lambda b (val (Lambda_initial hp))) =
  component_val (e_lambda (fun i => b (widen_ord hp i)) (ord_tuple p))).
by rewrite !e_lambdaE /Lambda_initial /initial_tuple /= -map_comp.
Qed.

(** Source for [simple_adapted_basis]: Federer 1.6.3, p. 25, adapted-basis
    computation. A nonzero simple p-vector is the product of the first p
    members of a basis of V. Supporting existence theorem The scalar factor
    in those proofs is absorbed in the chosen basis; degree zero is also
    valid for the literal simple unit. *)
Theorem simple_adapted_basis (K : fieldType) (V : lmodType K)
  n (e : 'I_n -> V) (he : is_basis e) p (hp : (p <= n)%N)
  (xi : exterior_power V p) : xi != 0 -> simple xi ->
  exists b : 'I_n -> V, is_basis b /\
    xi = e_lambda b (val (Lambda_initial hp)).
Proof.
move=> hx [t ht]; rewrite tuple_product in ht.
have hw : exterior_word [seq tnth t i | i <- enum 'I_p] != 0.
  apply/eqP=> hz; apply: (elimT negP hx); apply/eqP; rewrite ht.
  apply: val_inj.
  change (component_val (e_lambda (tnth t) (ord_tuple p)) =
    component_val (0 : exterior_power V p)).
  by rewrite e_lambdaE linear0.
have [b [hb hbt]] := finite_basis_extension_fixed hp (nonzero_word_independent hw) he.
exists b; split=> //; rewrite initial_productE ht.
have hf : (fun i => b (widen_ord hp i)) = tnth t.
  by apply: funext => i; exact: hbt.
by rewrite hf.
Qed.

(** Source for [top_covector_expansion]: Federer 1.6.3, p. 25,
    change to adapted dual bases. Supporting identity: any top covector
    is its value on a basis product times the corresponding dual product.
    This follows from the dual bases of 1.4.3 and 1.5.2. *)
Theorem top_covector_expansion (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
  (phi : A_m V K^o n) :
  phi = (pairing (e_lambda e (val (Lambda_top n))) phi : K) *:
    omega_lambda h2 (fun i => one_form (dual_basis he i)) (Lambda_top n).
Proof.
pose omega i := one_form (dual_basis he i).
have hd i j : omega i [tuple e j] = if i == j then 1 else 0.
  exact: finite_dual_biorthogonal.
elim/(basis_induction (@omega_lambda_basis K h2 V n n e omega he hd)): phi =>
  [|phi psi hphi hpsi|c phi hphi|lambda].
- by rewrite (bil0r (@pairing_bilinear K V K^o n)) scale0r.
- by rewrite (bilDr (@pairing_bilinear K V K^o n)) scalerDl -hphi -hpsi.
- by rewrite (bilZr (@pairing_bilinear K V K^o n)) -scalerA -hphi.
- by rewrite (Lambda_top_unique lambda) (pairing_e_omega h2 hd) eqxx scale1r.
Qed.

(** Source for [omega_lambda_simple]: Federer 1.6.3, p. 24,
    definition of simple covectors. Supporting instance: every indexed
    product of one-covectors is simple, including the empty product. *)
Lemma omega_lambda_simple (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (omega : 'I_n -> A_m V K^o 1)
  p (lambda : Lambda n p) : simple_covector h2 (omega_lambda h2 omega lambda).
Proof. by exists (fun i => omega (tnth (val lambda) i)). Qed.
