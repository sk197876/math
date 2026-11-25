(** Federer (1969), 1.6.5, pp. 25-26. Supporting complete
    four-block calculation for basis pairs: missing, first-only,
    common, second-only. An empty missing block gives the printed
    adapted computation. A nonempty missing block gives zero on
    both sides, by its dual covector. All block sizes may be zero. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors ProductAdaptedIdentity ProductMissingCovector
  ProductContractionAlgebra ProductSpaceMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section FourBlocks.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables t m r s : nat.
Variables (D : 'I_t -> V) (A : 'I_m -> V) (B : 'I_r -> V) (C : 'I_s -> V).
Local Notation N := (t+(m+(r+s)))%N.
Local Notation E := (concatenate_family A (concatenate_family B C)).
Local Notation b := (concatenate_family D E).
Hypothesis hb : is_basis b.
Variable omega : 'I_N -> A_m V K^o 1.
Hypothesis hd : forall i j, omega i [tuple b j] = if i == j then 1 else 0.
Local Notation volume := (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) omega).
Local Notation As := [seq A i | i <- enum 'I_m].
Local Notation Bs := [seq B i | i <- enum 'I_r].
Local Notation Cs := [seq C i | i <- enum 'I_s].

(** Source for [four_block_product_identity]: Federer 1.6.5,
    pp. 25-26, the adapted computation together with its zero
    extension. Supporting exhaustive calculation for a basis pair
    partitioned into the four possible membership classes. *)
Theorem four_block_product_identity :
  product_contraction_hom h2 (form_homogeneous volume)
    (exterior_word (As ++ Bs)) (exterior_word (Bs ++ Cs)) =
  (-1 : K)^+((N-(m+r))*(r+s)) *:
    diagonal_contraction_hom h2 (form_homogeneous volume)
      (exterior_word (As ++ Bs)) (exterior_word (Bs ++ Cs)).
Proof.
case: (posnP t) => [ht|ht].
- subst t.
  have heq i : b i = E i.
    case: (split_ordP i) => [j ->|j ->].
    + by have := ltn_ord j; rewrite ltn0.
    + rewrite concatenate_family_r.
      have hj : rshift 0 j = j by apply: val_inj; rewrite /= add0n.
      by rewrite hj.
  have he : is_basis E := basis_congr heq hb.
  have hdual i j : omega i [tuple E j] = if i == j then 1 else 0.
    by rewrite -heq hd.
  have hn : ((0+(m+(r+s)))-(m+r) = s)%N by rewrite add0n addnA addKn.
  rewrite hn /product_contraction_hom /diagonal_contraction_hom
    -form_pullback_hom !exterior_algebra_map_word.
  exact: (@adapted_product_identity K h2 V m r s A B C he omega hdual).
- pose i0 : 'I_t := Ordinal ht.
  pose j0 := lshift (m+(r+s)) i0.
  have hnorm : one_hom (omega j0) (D i0) = 1.
    by rewrite one_homE -(concatenate_family_l D E i0) hd eqxx.
  have hE i : one_hom (omega j0) (E i) = 0.
    by rewrite one_homE -(concatenate_family_r D E i) hd /j0 eq_lrshift.
  have hA i : one_hom (omega j0) (A i) = 0.
    have h := hE (lshift (r+s) i); by rewrite concatenate_family_l in h.
  have hB i : one_hom (omega j0) (B i) = 0.
    have h := hE (rshift m (lshift s i));
      by rewrite concatenate_family_r concatenate_family_l in h.
  have hC i : one_hom (omega j0) (C i) = 0.
    have h := hE (rshift m (rshift r i)); by rewrite !concatenate_family_r in h.
  have hx v : v \in As ++ Bs -> one_hom (omega j0) v = 0.
    rewrite mem_cat => /orP [/mapP [i _ ->]|/mapP [i _ ->]]; [exact: hA|exact: hB].
  have hy v : v \in Bs ++ Cs -> one_hom (omega j0) v = 0.
    rewrite mem_cat => /orP [/mapP [i _ ->]|/mapP [i _ ->]]; [exact: hB|exact: hC].
  rewrite /product_contraction_hom /diagonal_contraction_hom
    -form_pullback_hom !exterior_algebra_map_word
    (@product_missing_volume_factor K h2 V N omega j0 (D i0) hnorm
      (As ++ Bs) (Bs ++ Cs) hx hy)
    (@product_missing_dual_factor K h2 V N omega j0 (D i0) hnorm
      (As ++ Bs) (Bs ++ Cs) hx hy) linear0 scaler0.
  by [].
Qed.
End FourBlocks.
