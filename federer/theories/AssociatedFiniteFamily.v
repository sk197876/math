(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import AssociatedSubspace ExteriorFiniteReduction
  SubspaceCarrier FiniteSpanSpace ExteriorSubspaceReduction SubspaceFamilies
  FiniteBasisExtension AssociatedInitialFactor InitialIndices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1: reduce a nonzero xi and a prescribed independent
    family e_1,...,e_k in T to finite dimension, extend that very family
    to a basis, and apply the Grassmann-coordinate factorisation. *)
Section Family.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables m k : nat.
Variable xi : exterior_power V m.
Variable e : 'I_k -> V.
Hypothesis he : finite_independent e.
Hypothesis hT : forall i, FedererSimple.T xi (e i).
(** Source for [associated_finite_family]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem associated_finite_family : xi != 0 ->
  (k <= m)%N /\ exists xi' : exterior_power V (m-k),
    component_val xi = wedge (component_val (e_lambda e (ord_tuple k))) (component_val xi').
Proof.
move=> hx.
have [l [b [hb [hs [eta heta]]]]] := exterior_finite_dimensional_reduction xi
  [seq e i | i <- enum 'I_k].
pose S := finite_span_subspace b.
pose U := finite_span_vect hb.
pose iota := subspace_inclusion S.
have hS i : S (e i).
  apply: hs; apply/mapP; exists i => //; exact: mem_enum.
pose a : 'I_k -> U := subspace_family hS.
have ha : finite_independent a := @subspace_family_independent K V S 'I_k e hS he.
have hTa i : FedererSimple.T eta (a i).
  apply: (proj1 (@associated_subspace_preimage K V S m eta (a i))).
  change (FedererSimple.T (exterior_power_map iota m eta) (e i)).
  by rewrite heta; exact: hT.
have hneta : eta != 0.
  apply/eqP=> h; move: hx; by rewrite -heta h linear0 eqxx.
have [n [hkn [f [hf hfa]]]] := finite_basis_extension ha (finite_span_basisP hb).
pose omega i := one_form (dual_basis hf i).
have hd i j : omega i [tuple f j] = if i == j then 1 else 0.
  by rewrite /omega one_formE dual_basisE eq_sym.
have hTf i : FedererSimple.T eta (f (widen_ord hkn i)).
  by rewrite hfa; exact: hTa.
have [hkm [eta' heq]] := @nonzero_initial_factorisation K h2 U n m k f omega
  hf hd hkn eta hTf hneta.
split=> //; exists (exterior_power_map iota (m-k) eta').
have hprod : exterior_algebra_map iota (component_val (e_lambda f (val (Lambda_initial hkn)))) =
    component_val (e_lambda e (ord_tuple k)).
  rewrite !e_lambdaE exterior_algebra_map_word -map_comp.
  congr (exterior_word _).
  change ([seq iota (f i) | i <- initial_tuple hkn] = [seq e i | i <- enum 'I_k]).
  rewrite /initial_tuple /= -map_comp; apply: eq_map => i.
  by rewrite /= hfa.
have h := congr1 (exterior_algebra_map iota) heq.
rewrite algebra_map_mul hprod in h.
change (component_val (exterior_power_map iota m eta) =
  wedge (component_val (e_lambda e (ord_tuple k)))
    (component_val (exterior_power_map iota (m-k) eta'))) in h.
by rewrite heta in h.
Qed.
End Family.
