(** Federer (1969), 1.6.5, p. 26, contraction of the transverse
    factors and retention of the diagonal factors. This supporting
    block rule does not require the listed vectors to be independent.
    It follows from the source-annotated free-model calculation in
    InteriorFrame.v and the initial-complement index identity. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors InteriorFrame InitialComplementSequence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [interior_dual_block]: Federer 1.6.5, p. 26,
    final pairing computation. Supporting block formula: a product
    of n one-forms dual to the first n vectors and zero on the last
    r vectors contracts their ordered product to the last r-vector.
    Empty initial and final blocks are included. *)
Theorem interior_dual_block (K : fieldType) (h2 : (1+1 : K) != 0)
  (W : lmodType K) n r (c : 'I_n -> W) (s : 'I_r -> W)
  (a : 'I_n -> A_m W K^o 1)
  (hc : forall j i, one_hom (a j) (c i) = if j == i then 1 else 0)
  (hs : forall j i, one_hom (a j) (s i) = 0) :
  left_interior_hom h2
    (wedge (exterior_word [seq c i | i <- enum 'I_n])
      (exterior_word [seq s i | i <- enum 'I_r]))
    (form_homogeneous (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) a)) =
  exterior_word [seq s i | i <- enum 'I_r].
Proof.
pose v := concatenate_family c s.
have hf j i : one_hom (a j) (v i) =
    if widen_ord (leq_addr r n) j == i then 1 else 0.
  have hj : widen_ord (leq_addr r n) j = lshift r j by apply: val_inj.
  rewrite hj; case: (split_ordP i) => [q ->|q ->].
  - by rewrite /v concatenate_family_l hc (inj_eq (@lshift_inj n r)).
  - by rewrite /v concatenate_family_r hs eq_lrshift.
have h := @interior_initial_frame K h2 W n (n+r) (leq_addr r n) v a hf.
have hv := congr1 component_val h.
rewrite left_interiorE !e_lambdaE initial_complement_sequence
  -!map_comp /= in hv.
rewrite -(@enumT 'I_(n+r)) -(@enumT 'I_r) in hv.
change (left_interior_hom h2 (exterior_word [seq v i | i <- enum 'I_(n+r)])
  (form_homogeneous (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) a)) =
  exterior_word [seq v (rshift n i) | i <- enum 'I_r]) in hv.
have ht : [seq v (rshift n i) | i <- enum 'I_r] = [seq s i | i <- enum 'I_r].
  apply: eq_map => i; exact: concatenate_family_r.
rewrite ht /v concatenate_family_sequence -exterior_word_cat in hv.
exact: hv.
Qed.
