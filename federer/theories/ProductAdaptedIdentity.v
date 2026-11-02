(** Federer (1969), 1.6.5, pp. 25-26: the identity for the adapted products
    used in the printed proof. This module joins the checked transverse
    contraction with the corresponding duality computation. The full
    arbitrary-input identity requires a separate spanning argument, not an
    assumption of adaptability. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import SimpleVectors ProductAdaptedWords FinalBlockDuality
  InteriorBlock InitialComplementSequence CovectorProductNaturality ProductSpaceMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Import FedererProduct.

Section Adapted.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables m r s : nat.
Variables (A : 'I_m -> V) (B : 'I_r -> V) (C : 'I_s -> V).
Local Notation n := (m+(r+s))%N.
Local Notation e := (concatenate_family A (concatenate_family B C)).
Hypothesis he : is_basis e.
Variable omega : 'I_n -> A_m V K^o 1.
Hypothesis hd : forall i j, omega i [tuple e j] = if i == j then 1 else 0.
Local Notation volume := (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) omega).
Local Notation first_forms := (fun i => omega (lshift (r+s) i)).
Local Notation As := [seq A i | i <- enum 'I_m].
Local Notation Bs := [seq B i | i <- enum 'I_r].
Local Notation Cs := [seq C i | i <- enum 'I_s].

(** Source for [adapted_trailing_dual]: Federer 1.6.5, p. 26,
    D_l of the product e_(n-l+1),...,e_n is the first n-l dual
    product. Direct formula for the concatenated adapted basis. *)
Lemma adapted_trailing_dual :
  right_interior_hom (exterior_word (Bs ++ Cs)) (form_homogeneous volume) =
    form_homogeneous (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) first_forms).
Proof.
have h := @right_final_block K h2 V n e omega he hd m (leq_addr (r+s) m).
rewrite e_lambdaE initial_complement_sequence
  omega_lambda_top_product omega_lambda_initial_product in h.
have htail : [seq e i | i <- [seq rshift m j | j <- enum 'I_(r+s)]] = Bs ++ Cs.
  rewrite -map_comp.
  transitivity [seq concatenate_family B C i | i <- enum 'I_(r+s)].
  - apply: eq_map => i; exact: concatenate_family_r.
  - exact: concatenate_family_sequence.
have hfirst : (fun i => omega (widen_ord (leq_addr (r+s) m) i)) = first_forms.
  apply: funext => i; congr (omega _); exact: val_inj.
by rewrite htail hfirst in h.
Qed.

(** Source for [adapted_first_forms_dual]: Federer 1.6.5, p. 26,
    contraction by the first n-l dual basis forms. Supporting
    evaluation on the first block of basis vectors. *)
Lemma adapted_first_forms_dual j i : one_hom (first_forms j) (A i) =
  if j == i then 1 else 0.
Proof.
rewrite one_homE -(concatenate_family_l A (concatenate_family B C) i) hd eq_lshift.
by [].
Qed.

(** Source for [adapted_first_forms_annihilated]: Federer 1.6.5,
    p. 26, the common factors survive contraction by the first
    n-l forms. Supporting zero pairing of distinct basis blocks. *)
Lemma adapted_first_forms_annihilated j i : one_hom (first_forms j) (B i) = 0.
Proof.
rewrite one_homE -(concatenate_family_l B C i)
  -(concatenate_family_r A (concatenate_family B C) (lshift s i)) hd eq_lrshift.
by [].
Qed.

(** Source for [adapted_dual_contraction]: Federer 1.6.5, p. 26,
    first displayed computation, xi contracted by D_l eta equals
    the product of the common basis vectors. Direct formalisation. *)
Theorem adapted_dual_contraction :
  left_interior_hom h2 (exterior_word (As ++ Bs))
    (right_interior_hom (exterior_word (Bs ++ Cs)) (form_homogeneous volume)) =
      exterior_word Bs.
Proof.
rewrite adapted_trailing_dual -exterior_word_cat.
exact: interior_dual_block adapted_first_forms_dual adapted_first_forms_annihilated.
Qed.

(** Source for [adapted_product_identity]: Federer 1.6.5,
    pp. 25-26, the displayed identity for the adapted products in
    the proof. Direct equality in the full exterior algebra;
    the degree-specific dual-product interpretation is supplied
    separately by dual_product_contraction. *)
Theorem adapted_product_identity :
  left_interior_hom h2
    (wedge (exterior_word [seq P v | v <- As ++ Bs])
      (exterior_word [seq Q v | v <- Bs ++ Cs]))
    (form_homogeneous (A_m_dual (f_map V) volume)) =
  (-1 : K)^+(s*(r+s)) *:
    exterior_algebra_map (g_map V)
      (left_interior_hom h2 (exterior_word (As ++ Bs))
        (right_interior_hom (exterior_word (Bs ++ Cs)) (form_homogeneous volume))).
Proof.
rewrite adapted_dual_contraction exterior_algebra_map_word -(map_comp (g_map V) B).
exact: (@adapted_product_contraction K h2 V m r s A B C omega hd).
Qed.
End Adapted.
