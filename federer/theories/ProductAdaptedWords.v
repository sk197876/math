(** Federer (1969), 1.6.5, p. 26, the two last displayed lines. This is the
    direct adapted-family computation. The three lists below are the factors
    exclusive to xi, common to both vectors, and exclusive to eta. Their
    lengths are n-l, k+l-n, n-k. The general bilinear identity still
    requires extending this computation to arbitrary inputs. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors ProductSpaceMaps PairedExteriorWords
  InteriorBlock CovectorProductNaturality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Import FedererProduct.

(** Source for [exterior_word_negated]: Federer 1.6.5, p. 26,
    contribution of f(Q(e_j))=-e_j to the final sign. Supporting
    rule: negating every factor contributes (-1) to the power of
    the number of factors. *)
Lemma exterior_word_negated (K : fieldType) (V : lmodType K) (s : seq V) :
  exterior_word [seq -v | v <- s] = (-1 : K)^+(size s) *: exterior_word s.
Proof.
elim: s => [|v s ih] /=; first by rewrite expr0 scale1r.
by rewrite !exterior_word_cons linearN ih -scaleN1r
  (bilZl (wedge_bilinear V)) (bilZr (wedge_bilinear V)) scalerA exprS.
Qed.

(** Source for [product_adapted_sign]: Federer 1.6.5, pp. 25-26,
    comparison of the reordering sign on p. 26 with (-1)^((n-k)l)
    on p. 25. Supporting parity identity, with r=k+l-n and s=n-k. *)
Lemma product_adapted_sign (K : fieldType) r s :
  (-1 : K)^+(r*s+s) = (-1 : K)^+(s*(r+s)).
Proof.
rewrite -[LHS]signr_odd -[RHS]signr_odd !oddD !oddM !oddD.
by case: (odd r); case: (odd s).
Qed.

Section Computation.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables m r s : nat.
Variables (A : 'I_m -> V) (B : 'I_r -> V) (C : 'I_s -> V).
Local Notation n := (m+(r+s))%N.
Local Notation e := (concatenate_family A (concatenate_family B C)).
Variable omega : 'I_n -> A_m V K^o 1.
Hypothesis hd : forall i j, omega i [tuple e j] = if i == j then 1 else 0.
Local Notation W := (GRing.Lmodule.clone K (V * V)%type _).
Local Notation gamma := (fun i => A_m_dual (f_map V) (omega i)).

(** Source for [product_transverse_family]: Federer 1.6.5,
    p. 26, vectors P(e_j), a_j, Q(e_j) in the final computation.
    Supporting family: negate the last Q block so that the
    difference map sends every factor to its corresponding e_j. *)
Definition product_transverse_family : 'I_n -> W :=
  concatenate_family (fun i => P (A i))
    (concatenate_family (fun i => a (B i)) (fun i => - Q (C i))).

(** Source for [product_transverse_image]: Federer 1.6.5, p. 26,
    evaluation of omega_j composed with f. Supporting identity:
    the transverse family maps to the original ordered family. *)
Lemma product_transverse_image i : f (product_transverse_family i) = e i.
Proof.
case: (split_ordP i) => [j ->|j ->].
- by rewrite /product_transverse_family !concatenate_family_l f_P.
- rewrite /product_transverse_family !concatenate_family_r.
  case: (split_ordP j) => [q ->|q ->].
  + by rewrite !concatenate_family_l (f_a h2).
  + by rewrite !concatenate_family_r linearN /= f_Q opprK.
Qed.

(** Source for [product_transverse_dual]: Federer 1.6.5, p. 26,
    evaluation of the pulled-back volume factors on the transverse
    family. Supporting Kronecker-delta pairing. *)
Lemma product_transverse_dual j i :
  one_hom (gamma j) (product_transverse_family i) = if j == i then 1 else 0.
Proof.
rewrite one_homE A_m_dualE.
have ht : map_tuple (f_map V) [tuple product_transverse_family i] = [tuple e i].
  apply: val_inj; change ([:: f (product_transverse_family i)] = [:: e i]).
  by rewrite product_transverse_image.
by rewrite ht hd.
Qed.

(** Source for [product_diagonal_annihilated]: Federer 1.6.5,
    p. 26, retention of the b_j=(e_j,e_j) factors. Supporting fact:
    every pulled-back volume one-form vanishes on these factors. *)
Lemma product_diagonal_annihilated j i : one_hom (gamma j) (g (B i)) = 0.
Proof.
rewrite one_homE A_m_dualE.
have ht : map_tuple (f_map V) [tuple g (B i)] = [tuple (0 : V)].
  apply: val_inj; change ([:: f (g (B i))] = [:: (0 : V)]).
  by rewrite f_g.
rewrite ht -one_homE; exact: linear0.
Qed.

(** Source for [product_transverse_contraction]: Federer 1.6.5,
    p. 26, final pairing computation after reordering. Direct
    contraction of all transverse factors leaves the product of
    the common diagonal factors, with normalisation one. *)
Lemma product_transverse_contraction :
  left_interior_hom h2
    (wedge (exterior_word [seq product_transverse_family i | i <- enum 'I_n])
      (exterior_word [seq g (B i) | i <- enum 'I_r]))
    (form_homogeneous (A_m_dual (f_map V)
      (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) omega))) =
    exterior_word [seq g (B i) | i <- enum 'I_r].
Proof.
rewrite one_forms_wedge_natural.
exact: interior_dual_block product_transverse_dual product_diagonal_annihilated.
Qed.

(** Source for [product_transverse_word]: Federer 1.6.5, p. 26,
    contribution of the final Q block to the sign. Supporting
    identity: negating that block contributes (-1)^s. *)
Lemma product_transverse_word :
  exterior_word [seq product_transverse_family i | i <- enum 'I_n] =
  (-1 : K)^+s *:
    wedge (exterior_word [seq P (A i) | i <- enum 'I_m])
      (wedge (exterior_word [seq a (B i) | i <- enum 'I_r])
        (exterior_word [seq Q (C i) | i <- enum 'I_s])).
Proof.
have hn := exterior_word_negated [seq Q (C i) | i <- enum 'I_s].
rewrite -map_comp size_map size_enum_ord in hn.
rewrite /product_transverse_family !concatenate_family_sequence -!exterior_word_cat hn.
by rewrite !(bilZr (wedge_bilinear W)).
Qed.

(** Source for [product_adapted_word_reordering]: Federer 1.6.5,
    p. 26, first equality and final sign in the last display.
    Direct reordering of the three blocks before contraction. *)
Lemma product_adapted_word_reordering :
  wedge (exterior_word [seq P v | v <-
    [seq A i | i <- enum 'I_m] ++ [seq B i | i <- enum 'I_r]])
    (exterior_word [seq Q v | v <-
    [seq B i | i <- enum 'I_r] ++ [seq C i | i <- enum 'I_s]]) =
  (-1 : K)^+(r*s+s) *:
    wedge (exterior_word [seq product_transverse_family i | i <- enum 'I_n])
      (exterior_word [seq g (B i) | i <- enum 'I_r]).
Proof.
pose PA := exterior_word [seq P (A i) | i <- enum 'I_m].
pose PB := exterior_word [seq P (B i) | i <- enum 'I_r].
pose QB := exterior_word [seq Q (B i) | i <- enum 'I_r].
pose QC := exterior_word [seq Q (C i) | i <- enum 'I_s].
pose AB := exterior_word [seq a (B i) | i <- enum 'I_r].
pose GB := exterior_word [seq g (B i) | i <- enum 'I_r].
have hp : wedge PB QB = wedge AB GB.
  apply: paired_exterior_words_replace => i; exact: product_pair_wedge.
have hs : wedge GB QC = (-1 : K)^+(r*s) *: wedge QC GB.
  rewrite /GB /QC exterior_words_anticommutative !size_map
    -(@enumT 'I_r) -(@enumT 'I_s) !size_enum_ord.
  by [].
rewrite product_transverse_word !map_cat -!map_comp -!exterior_word_cat
  (bilZl (wedge_bilinear W)) scalerA exprD -mulrA.
rewrite -[(-1)^+s * (-1)^+s]expr2 sqrr_sign mulr1.
rewrite -(@enumT 'I_m) -(@enumT 'I_r) -(@enumT 'I_s).
change (wedge (wedge PA PB) (wedge QB QC) =
  (-1 : K)^+(r*s) *: wedge (wedge PA (wedge AB QC)) GB).
rewrite -wedge_assoc (wedge_assoc PB) hp -wedge_assoc hs
  !(bilZr (wedge_bilinear W)).
by rewrite !wedge_assoc.
Qed.

(** Source for [adapted_product_contraction]: Federer 1.6.5,
    p. 26, final equality in the adapted-family computation.
    Direct formula: the contraction is the common diagonal product
    with sign (-1)^((n-k)l), written s(r+s) for these three blocks. *)
Theorem adapted_product_contraction :
  left_interior_hom h2
    (wedge (exterior_word [seq P v | v <-
      [seq A i | i <- enum 'I_m] ++ [seq B i | i <- enum 'I_r]])
      (exterior_word [seq Q v | v <-
      [seq B i | i <- enum 'I_r] ++ [seq C i | i <- enum 'I_s]]))
    (form_homogeneous (A_m_dual (f_map V)
      (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) omega))) =
  (-1 : K)^+(s*(r+s)) *: exterior_word [seq g (B i) | i <- enum 'I_r].
Proof.
rewrite product_adapted_word_reordering
  (bilZl (left_interior_hom_bilinear h2 _)) product_transverse_contraction.
by rewrite product_adapted_sign.
Qed.
End Computation.
