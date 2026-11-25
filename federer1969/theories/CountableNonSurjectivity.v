(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import OmegaConstruction FiniteRankPullback FiniteEvaluationMaps
  DisjointBlocks BlockCovector FirstArgument.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4, infinite-dimensional assertion *)
Section CountableNonSurjectivity.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable m : nat.
Local Notation N := (Choice.clone nat _).
Local Notation F := (GRing.Lmodule.clone K (free_vector K N) _).
Local Notation d := (@delta K N).
Local Notation phi := (@block_covector K h2 m.+2).
(** Source for [block_tail]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition block_tail j : seq F := [seq d k | k <- iota (m.+2*j).+1 m.+1].
(** Source for [block_first_argument]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma block_first_argument i j : first_argument phi (block_tail j) (d (m.+2*i)%N) =
  if i == j then 1 else 0.
Proof.
have h := @block_covector_mixed K h2 m i j.
by rewrite form_includeE form_extensionE in h.
Qed.
(** Source for [block_covector_not_in_image]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Theorem block_covector_not_in_image :
  ~ exists x : exterior_power (Hom F K^o) m.+2, Omega_m h2 x = phi.
Proof.
move=> [x hx]; have [n [e [omega he]]] := Omega_m_finite_rank_pullback h2 x.
rewrite hx in he.
pose H := reconstruction_map e omega.
pose C : vectType K := finite_basis_vect (coordinate_basisP K n).
pose v (i : 'I_n.+1) : C := covector_analysis omega (d (m.+2*val i)%N).
pose ell (j : 'I_n.+1) : {linear C -> K^o} :=
  linear_comp (GRing.Linear.clone _ _ _ _ (first_argument phi [seq H u | u <- block_tail (val j)]) _)
    (point_synthesis e).
have hh : form_include phi = A_star_dual H (form_include phi).
  have h := congr1 (@form_include K F K^o m.+2) he.
  by rewrite -A_star_dual_include in h.
have hpair (i j : 'I_n.+1) : ell i (v j) = if i == j then 1 else 0.
  have h := congr1 (fun a : A_star F K^o =>
    a (exterior_word (d (m.+2*val j)%N :: block_tail (val i)))) hh.
  rewrite A_star_dualE exterior_algebra_map_word !form_includeE !form_extensionE in h.
  change (first_argument phi (block_tail (val i)) (d (m.+2*val j)%N) = ell i (v j)) in h.
  rewrite -h block_first_argument (inj_eq val_inj) eq_sym; by [].
have hind : finite_independent v := finite_independent_separating hpair.
have hd := @finite_independent_dimension_bound K C n.+1 v hind.
by rewrite /C finite_basis_dimension card_ord ltnn in hd.
Qed.
End CountableNonSurjectivity.
