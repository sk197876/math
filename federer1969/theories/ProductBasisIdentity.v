(** Federer (1969), 1.6.5, pp. 25-26: complete spanning argument
    for all pairs of Grassmann basis vectors. Partition the basis
    indices into four blocks, apply the checked adapted or missing-
    direction computation, and account for the two permutation
    signs and the scalar change of top form. The volume may be
    any top form, including zero. This supplies the extension left
    implicit after the printed adapted-family computation. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors BasisPairPartition BasisIndexFamilies
  ProductFourBlocks ProductVolumeChange ProductContractionAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [basis_pair_product_identity]: Federer 1.6.5,
    pp. 25-26, supporting extension from adapted factors to every
    Grassmann basis pair. Both transverse and nontransverse pairs
    are covered, including empty products and zero dimension. *)
Theorem basis_pair_product_identity (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
  (phi : A_m V K^o n) k l (lambda : Lambda n k) (mu : Lambda n l) :
  product_contraction_hom h2 (form_homogeneous phi)
    (exterior_word [seq e i | i <- val lambda])
    (exterior_word [seq e i | i <- val mu]) =
  (-1 : K)^+((n-k)* l) *:
    diagonal_contraction_hom h2 (form_homogeneous phi)
      (exterior_word [seq e i | i <- val lambda])
      (exterior_word [seq e i | i <- val mu]).
Proof.
pose u := val (val lambda).
pose v := val (val mu).
have hu : uniq u := Lambda_uniq lambda.
have hv : uniq v := Lambda_uniq mu.
pose ds := BasisPairPartition.missing u v.
pose as_ := BasisPairPartition.first_only u v.
pose bs := BasisPairPartition.common u v.
pose cs := BasisPairPartition.second_only u v.
pose D i := e (index_block_family ds i).
pose A i := e (index_block_family as_ i).
pose B i := e (index_block_family bs i).
pose C i := e (index_block_family cs i).
pose b := concatenate_family D (concatenate_family A (concatenate_family B C)).
pose N := (size ds+(size as_+(size bs+size cs)))%N.
have hb : is_basis b.
  apply: (@four_block_basis K V n e he ds as_ bs cs).
  - exact: BasisPairPartition.all_indices_unique.
  - exact: BasisPairPartition.all_indices_cover.
have hdim : n = N := finite_basis_size he hb.
have hpx : perm_eq (as_ ++ bs) u := @BasisPairPartition.first_common_permutation 'I_n u v hu.
have hpy : perm_eq (bs ++ cs) v := @BasisPairPartition.common_second_permutation 'I_n u v hv.
have hk : (size as_+size bs = k)%N.
  have h := perm_size hpx; by rewrite size_cat /u size_tuple in h.
have hl : (size bs+size cs = l)%N.
  have h := perm_size hpy; by rewrite size_cat /v size_tuple in h.
have hsortx : sorted leq (map val u).
  have h := valP lambda; by rewrite ltn_sorted_uniq_leq in h; case/andP: h.
have hsorty : sorted leq (map val v).
  have h := valP mu; by rewrite ltn_sorted_uniq_leq in h; case/andP: h.
pose cx := (-1 : K)^+(inversions (map val (as_ ++ bs))).
pose cy := (-1 : K)^+(inversions (map val (bs ++ cs))).
have hx : exterior_word [seq e i | i <- u] =
    cx *: exterior_word [seq e i | i <- as_ ++ bs].
  rewrite (exterior_index_word_order e hsortx hpx) /cx scalerA -expr2 sqrr_sign scale1r.
  by [].
have hy : exterior_word [seq e i | i <- v] =
    cy *: exterior_word [seq e i | i <- bs ++ cs].
  rewrite (exterior_index_word_order e hsorty hpy) /cy scalerA -expr2 sqrr_sign scale1r.
  by [].
pose omega i := one_form (dual_basis hb i).
have hd i j : omega i [tuple b j] = if i == j then 1 else 0.
  exact: finite_dual_biorthogonal.
have h4 := @four_block_product_identity K h2 V (size ds) (size as_) (size bs) (size cs)
  D A B C hb omega hd.
have hsigma : ((N-(size as_+size bs))*(size bs+size cs) = (n-k)* l)%N.
  by rewrite -hdim hk hl.
change (product_contraction_hom h2
  (form_homogeneous (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) omega))
  (exterior_word ([seq A i | i <- enum 'I_(size as_)] ++ [seq B i | i <- enum 'I_(size bs)]))
  (exterior_word ([seq B i | i <- enum 'I_(size bs)] ++ [seq C i | i <- enum 'I_(size cs)])) =
  (-1 : K)^+((N-(size as_+size bs))*(size bs+size cs)) *:
  diagonal_contraction_hom h2
  (form_homogeneous (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) omega))
  (exterior_word ([seq A i | i <- enum 'I_(size as_)] ++ [seq B i | i <- enum 'I_(size bs)]))
  (exterior_word ([seq B i | i <- enum 'I_(size bs)] ++ [seq C i | i <- enum 'I_(size cs)]))) in h4.
rewrite hsigma /A /B /C !mapped_index_block_sequence -!map_cat in h4.
have [c hc] := @top_form_rebased K h2 V N b hb n phi hdim.
change (product_contraction_hom h2 (form_homogeneous phi)
  (exterior_word [seq e i | i <- u]) (exterior_word [seq e i | i <- v]) =
  (-1 : K)^+((n-k)* l) *: diagonal_contraction_hom h2 (form_homogeneous phi)
  (exterior_word [seq e i | i <- u]) (exterior_word [seq e i | i <- v])).
rewrite hc hx hy.
apply: product_identity_input_scales.
apply: product_identity_volume_scale.
exact: h4.
Qed.
