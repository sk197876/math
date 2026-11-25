(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import AssociatedSubspace SimpleElementary SimpleWordIndependence
  SimpleProducts SubspaceDirectSums ConcatenatedFamilies ConcatenatedProducts
  IndependentProducts IndependentConcatenation FiniteSpans.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, third corollary, for two ordered products. *)
Section Products.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables m n : nat.
Variables (e : 'I_m -> V) (f : 'I_n -> V).
Local Notation xi := (e_lambda e (ord_tuple m)).
Local Notation eta := (e_lambda f (ord_tuple n)).
Local Notation zeta := (e_lambda (concatenate_family e f) (ord_tuple (m+n))).
Hypotheses (hx : xi != 0) (hy : eta != 0).
(** Source for [product_direct_sum]: Federer (1969), 1.6.1, p. 24, third
    corollary. In words: The wedge of two nonzero simple vectors is nonzero
    exactly when its associated subspace is the direct sum of their
    associated subspaces. Supporting lemma for this passage; not separately
    stated in the book. *)
Theorem product_direct_sum : exterior_product xi eta != 0 <->
  subspace_direct_sum (FedererSimple.T (exterior_product xi eta))
    (FedererSimple.T xi) (FedererSimple.T eta).
Proof.
rewrite concatenated_product.
have heT v := @product_associated_space K h2 V m e hx v.
have hfT v := @product_associated_space K h2 V n f hy v.
split.
- move=> hz; split.
  + move=> v; split.
    * move=> hv; have [x [y [hs [ht hxy]]]] := proj1 (@concatenated_product_space K h2 V m n e f hz v) hv.
      exists x,y; split; first exact: (proj2 (heT x)).
      split=> //; exact: (proj2 (hfT y)).
    * move=> [x [y [hs [ht hxy]]]].
      apply: (proj2 (@concatenated_product_space K h2 V m n e f hz v)).
      exists x,y; split; first exact: (proj1 (heT x)).
      split=> //; exact: (proj1 (hfT y)).
  + move=> v hv hw.
    have hi := concatenated_product_independent hz.
    exact (@independent_concatenation_disjoint K V m n e f hi v
      (proj1 (heT v) hv) (proj1 (hfT v) hw)).
- move=> [hs hd].
  have hew : exterior_word [seq e i | i <- enum 'I_m] != 0.
    apply/eqP=> hz; apply: (elimT negP hx); apply/eqP; apply: val_inj.
    change (component_val xi = component_val (0 : exterior_power V m)).
    by rewrite e_lambdaE linear0.
  have hfw : exterior_word [seq f i | i <- enum 'I_n] != 0.
    apply/eqP=> hz; apply: (elimT negP hy); apply/eqP; apply: val_inj.
    change (component_val eta = component_val (0 : exterior_power V n)).
    by rewrite e_lambdaE linear0.
  have hi : finite_independent (concatenate_family e f).
    apply: disjoint_concatenation_independent (nonzero_word_independent hew)
      (nonzero_word_independent hfw) _ => v hv hw.
    exact (hd v (proj2 (heT v) hv) (proj2 (hfT v) hw)).
  exact (@independent_product_nonzero K h2 V (m+n) (concatenate_family e f) hi).
Qed.
End Products.

(** Federer 1.6.1, third corollary, with exactly the book's hypotheses
    on the two arbitrary nonzero simple m- and n-vectors. *)
(** Source for [simple_product_direct_sum]: Federer (1969), 1.6.1, p. 24,
    third corollary. In words: The wedge of two nonzero simple vectors is
    nonzero exactly when its associated subspace is the direct sum of their
    associated subspaces. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Theorem simple_product_direct_sum (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) m n (xi : exterior_power V m) (eta : exterior_power V n) :
  xi != 0 -> eta != 0 -> simple xi -> simple eta ->
  (exterior_product xi eta != 0 <->
    subspace_direct_sum (FedererSimple.T (exterior_product xi eta))
      (FedererSimple.T xi) (FedererSimple.T eta)).
Proof.
move=> hx hy [t hxt] [s hys].
rewrite tuple_product in hxt.
rewrite tuple_product in hys.
have h := @product_direct_sum K h2 V m n (tnth t) (tnth s).
rewrite -hxt -hys in h.
exact: h hx hy.
Qed.
