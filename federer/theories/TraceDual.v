(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import TraceDefinition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5, final sentence: the superscript in A^1 f denotes
    the contravariant dual map of 1.4.1. Its trace equals trace(f). *)
Section TraceDual.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable I : finType.
Variable e : I -> V.
Hypothesis he : is_basis e.
(** Source for [one_covector_basis]: Federer (1969), 1.4.5, p. 21, last
    sentence before section 1.5. In words: The trace of the degree-one dual
    map is equal to the trace of the original endomorphism. Definition or
    construction used to formalise this passage. *)
Definition one_covector_basis i : A_m V K^o 1 := one_form (dual_basis he i).
(** Source for [one_covector_basisP]: Federer (1969), 1.4.5, p. 21, last
    sentence before section 1.5. In words: The trace of the degree-one dual
    map is equal to the trace of the original endomorphism. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma one_covector_basisP : is_basis one_covector_basis.
Proof.
exact (@basis_transport K (Choice.clone I _) (Hom V K^o) (A_m V K^o 1)
  (dual_basis he) (GRing.Linear.clone _ _ _ _ (@one_form K V K^o) _)
  (GRing.Linear.clone _ _ _ _ (@one_hom K V K^o) _)
  (@one_formK K V K^o) (@one_homK K V K^o) (dual_basisP he)).
Qed.
(** Source for [one_covector_dualE]: Federer (1969), 1.4.5, p. 21, last
    sentence before section 1.5. In words: The trace of the degree-one dual
    map is equal to the trace of the original endomorphism. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma one_covector_dualE i phi :
  dual_basis one_covector_basisP i phi = one_hom phi (e i).
Proof.
pose ev : {linear A_m V K^o 1 -> K^o} := linear_comp
  (GRing.Linear.clone _ _ _ _ (hom_evaluate (e i)) _)
  (GRing.Linear.clone _ _ _ _ (@one_hom K V K^o) _).
apply: (basis_linear_ext one_covector_basisP
  (hom_as_linear (dual_basis one_covector_basisP i)) ev) phi => j.
change (dual_basis one_covector_basisP i (one_covector_basis j) =
  one_hom (one_covector_basis j) (e i)).
by rewrite dual_basisE /one_covector_basis one_formK dual_basisE eq_sym.
Qed.
(** Source for [trace_dual]: Federer (1969), 1.4.5, p. 21, last sentence
    before section 1.5. In words: The trace of the degree-one dual map is
    equal to the trace of the original endomorphism. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem trace_dual (f : Hom V V) :
  @trace_Hom K h2 (A_m V K^o 1) I one_covector_basis one_covector_basisP
    (hom_of_linear (GRing.Linear.clone _ _ _ _ (@A_m_dual K V V K^o (hom_as_linear f) 1) _)) =
  @trace_Hom K h2 V I e he f.
Proof.
rewrite !trace_HomE; apply: eq_bigr => i _.
rewrite one_covector_dualE.
change (one_hom (A_m_dual (hom_as_linear f) (one_covector_basis i)) (e i) =
  dual_basis he i (f (e i))).
rewrite one_homE A_m_dualE /one_covector_basis.
change (one_form (dual_basis he i) [tuple f (e i)] = dual_basis he i (f (e i))).
exact: one_formE.
Qed.
End TraceDual.
