(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import Gamma TraceAlgebra TraceDefinition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5, penultimate paragraph: prove the displayed formula
    for rank-one maps, then use bilinearity to obtain cyclic invariance. *)
Section RankOne.
Variable K : fieldType.
Variable V : lmodType K.
(** Source for [rank_one]: Federer (1969), 1.4.5, p. 21, penultimate
    paragraph and rank-one calculation. In words: Trace(f composed with g)
    equals trace(g composed with f); bilinearity reduces the assertion to
    the displayed calculation for rank-one maps. Definition or construction
    used to formalise this passage. *)
Definition rank_one (a : A_m V K^o 1) (v : V) : Hom V V := hom_with_coefficient v (one_hom a).
(** Source for [rank_oneE]: Federer (1969), 1.4.5, p. 21, penultimate
    paragraph and rank-one calculation. In words: Trace(f composed with g)
    equals trace(g composed with f); bilinearity reduces the assertion to
    the displayed calculation for rank-one maps. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma rank_oneE a v x : rank_one a v x = (one_hom a x : K) *: v.
Proof. by []. Qed.
(** Source for [Gamma_inverse_pure]: Federer (1969), 1.4.5, p. 21,
    penultimate paragraph and rank-one calculation. In words: Trace(f
    composed with g) equals trace(g composed with f); bilinearity reduces
    the assertion to the displayed calculation for rank-one maps. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma Gamma_inverse_pure a v : @Gamma_inverse K V V (tensor_inj a v) = rank_one a v.
Proof. apply: hom_ext => x; exact: Gamma_inverseE. Qed.
(** Source for [rank_one_comp]: Federer (1969), 1.4.5, p. 21, penultimate
    paragraph and rank-one calculation. In words: Trace(f composed with g)
    equals trace(g composed with f); bilinearity reduces the assertion to
    the displayed calculation for rank-one maps. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Lemma rank_one_comp a v b w : hom_comp (rank_one a v) (rank_one b w) =
  (one_hom a w : K) *: rank_one b v.
Proof.
apply: hom_ext => x.
change ((one_hom a ((one_hom b x : K) *: w) : K) *: v =
  (one_hom a w : K) *: ((one_hom b x : K) *: v)).
rewrite (linZ (hom_linear (one_hom a))) scalerA.
by rewrite mulrC.
Qed.
Variable I : finType.
Variable e : I -> V.
Hypothesis he : is_basis e.
(** Source for [Gamma_rank_one]: Federer (1969), 1.4.5, p. 21, penultimate
    paragraph and rank-one calculation. In words: Trace(f composed with g)
    equals trace(g composed with f); bilinearity reduces the assertion to
    the displayed calculation for rank-one maps. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Lemma Gamma_rank_one a v : @Gamma K V V I e he (rank_one a v) = tensor_inj a v.
Proof. by rewrite -Gamma_inverse_pure Gamma_inverseK. Qed.
(** Source for [Gamma_rank_one_commutator]: Federer (1969), 1.4.5, p. 21,
    penultimate paragraph and rank-one calculation. In words: Trace(f
    composed with g) equals trace(g composed with f); bilinearity reduces
    the assertion to the displayed calculation for rank-one maps. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem Gamma_rank_one_commutator (f g : Hom V V) a b v w :
  @Gamma K V V I e he f = tensor_inj a v -> @Gamma K V V I e he g = tensor_inj b w ->
  @Gamma K V V I e he (hom_comp f g) - @Gamma K V V I e he (hom_comp g f) =
  (one_hom a w : K) *: tensor_inj b v - (one_hom b v : K) *: tensor_inj a w.
Proof.
move=> hf hg.
have ef : f = rank_one a v by rewrite -(@GammaK K V V I e he f) hf Gamma_inverse_pure.
have eg : g = rank_one b w by rewrite -(@GammaK K V V I e he g) hg Gamma_inverse_pure.
by rewrite ef eg !rank_one_comp !linearZ !Gamma_rank_one.
Qed.
End RankOne.

(** Source for [hom_comp_bilinear]: Federer (1969), 1.4.5, p. 21,
    penultimate paragraph and rank-one calculation. In words: Trace(f
    composed with g) equals trace(g composed with f); bilinearity reduces
    the assertion to the displayed calculation for rank-one maps. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma hom_comp_bilinear (K : fieldType) (U V W : lmodType K) :
  @bilinear K (Hom V W) (Hom U V) (Hom U W) (@hom_comp K U V W).
Proof.
split=> [g c f h|f c g h]; apply: hom_ext => x.
- by rewrite !hom_compE !hom_addE !hom_scaleE.
- by rewrite !hom_compE !hom_addE !hom_scaleE (hom_linear f).
Qed.

Section CyclicTrace.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable I : finType.
Variable e : I -> V.
Hypothesis he : is_basis e.
Local Notation tr := (@trace_Hom K h2 V I e he).
(** Source for [trace_Hom_rank_one]: Federer (1969), 1.4.5, p. 21,
    penultimate paragraph and rank-one calculation. In words: Trace(f
    composed with g) equals trace(g composed with f); bilinearity reduces
    the assertion to the displayed calculation for rank-one maps. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma trace_Hom_rank_one a v : tr (rank_one a v) = one_hom a v.
Proof.
change (@trace K h2 V (@Gamma_include K h2 V V (@Gamma K V V I e he (rank_one a v))) = one_hom a v).
by rewrite Gamma_rank_one trace_Gamma_include.
Qed.
(** Source for [trace_rank_one_cyclic]: Federer (1969), 1.4.5, p. 21,
    penultimate paragraph and rank-one calculation. In words: Trace(f
    composed with g) equals trace(g composed with f); bilinearity reduces
    the assertion to the displayed calculation for rank-one maps. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma trace_rank_one_cyclic a v b w :
  tr (hom_comp (rank_one a v) (rank_one b w)) = tr (hom_comp (rank_one b w) (rank_one a v)).
Proof.
rewrite !rank_one_comp !linearZ !trace_Hom_rank_one.
change ((one_hom a w : K)*(one_hom b v : K) = (one_hom b v : K)*(one_hom a w : K)).
exact: mulrC.
Qed.
(** Source for [trace_cyclic]: Federer (1969), 1.4.5, p. 21, penultimate
    paragraph and rank-one calculation. In words: Trace(f composed with g)
    equals trace(g composed with f); bilinearity reduces the assertion to
    the displayed calculation for rank-one maps. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Theorem trace_cyclic (f g : Hom V V) : tr (hom_comp f g) = tr (hom_comp g f).
Proof.
have hb : bilinear (fun f g : Hom V V => tr (hom_comp f g)).
  exact (bilinear_post tr (@hom_comp_bilinear K V V V)).
have hc : bilinear (fun f g : Hom V V => tr (hom_comp g f)).
  have [h1 h2'] := hb; split; [exact h2' | exact h1].
pose gi := @Gamma_inverse K V V.
have ht : forall x y, tr (hom_comp (gi x) (gi y)) = tr (hom_comp (gi y) (gi x)).
  apply (tensor_bilinear_ext (bilinear_pre gi gi hb) (bilinear_pre gi gi hc)) => a v b w.
  change (tr (hom_comp (@Gamma_inverse K V V (tensor_inj a v)) (@Gamma_inverse K V V (tensor_inj b w))) =
    tr (hom_comp (@Gamma_inverse K V V (tensor_inj b w)) (@Gamma_inverse K V V (tensor_inj a v)))).
  by rewrite !Gamma_inverse_pure trace_rank_one_cyclic.
have h := ht (@Gamma K V V I e he f) (@Gamma K V V I e he g).
by rewrite /gi !GammaK in h.
Qed.
End CyclicTrace.
