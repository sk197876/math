(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import AssociatedSubspace AssociatedFiniteFamily
  SimpleZeroDegree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, first and second corollaries: when k=m the remaining
    factor xi_prime has degree zero, so it is a scalar. The scalar is
    nonzero whenever xi is nonzero. *)
Section ScalarFactor.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable m : nat.
Variable xi : exterior_power V m.
Variable e : 'I_m -> V.
Hypothesis he : finite_independent e.
Hypothesis hT : forall i, FedererSimple.T xi (e i).
(** Source for [full_degree_factor]: Federer (1969), 1.6.1, p. 24, first of
    the four corollaries. In words: The printed corollary identifies nonzero
    simple m-vectors with those whose associated space has dimension m, and
    represents them as products of a suitable basis. Supporting lemma for
    this passage; not separately stated in the book. For the literal
    empty-product definition the reverse implication requires m>0. *)
Theorem full_degree_factor : xi != 0 -> exists c : K,
  c != 0 /\ xi = c *: e_lambda e (ord_tuple m).
Proof.
move=> hx; have [_ [eta heq]] := @associated_finite_family K h2 V m m xi e he hT hx.
pose eta0 := exterior_reindex (subnn m) eta.
pose c := exterior_zeroth_inverse V eta0.
have hc := congr1 (@component_val K (exterior_space V) (exterior_grading V) 0)
  (exterior_zeroth_inverseK eta0).
rewrite zeroth_inclusion_val in hc.
have he0 : component_val eta0 = component_val eta := exterior_reindexE (subnn m) eta.
rewrite he0 /exterior_scalar in hc.
have hxi : xi = (c : K) *: e_lambda e (ord_tuple m).
  apply: val_inj.
  change (component_val xi = component_val ((c : K) *: e_lambda e (ord_tuple m))).
  rewrite linearZ heq -hc (bilZr (wedge_bilinear V)) wedge_unitr; by [].
exists c; split=> //; apply/eqP=> hz.
by move: hx; rewrite hxi hz scale0r eqxx.
Qed.
End ScalarFactor.
