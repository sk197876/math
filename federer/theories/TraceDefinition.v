(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import TraceAlgebra Gamma.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5: include Gamma(f) in the degree-one summand of A,
    using the identification of W with its first exterior power. *)
Section GammaInAlgebra.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
(** Source for [Gamma_include]: Federer (1969), 1.4.5, p. 20, natural
    Hom-tensor isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Definition or construction used to formalise this
    passage. *)
Definition Gamma_include : {linear tensor_space (A_m V K^o 1) W -> A h2 V W} :=
  linear_comp (@A_component K h2 V W 1)
    (tensor_map (linear_id (A_m V K^o 1)) (exterior_first_inclusion W)).
(** Source for [Gamma_includeE]: Federer (1969), 1.4.5, p. 20, natural
    Hom-tensor isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Gamma_includeE phi w : Gamma_include (tensor_inj phi w) =
  @A_pure K h2 V W 1 phi (exterior_first_inclusion W w).
Proof.
change (@A_component K h2 V W 1 (tensor_map (linear_id (A_m V K^o 1))
  (exterior_first_inclusion W) (tensor_inj phi w)) = @A_pure K h2 V W 1 phi (exterior_first_inclusion W w)).
by rewrite tensor_mapE /= A_componentE.
Qed.
Variable I : finType.
Variable e : I -> V.
Hypothesis he : is_basis e.
(** Source for [Gamma_A]: Federer (1969), 1.4.5, p. 20, natural Hom-tensor
    isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Definition or construction used to formalise this
    passage. *)
Definition Gamma_A : {linear Hom V W -> A h2 V W} := linear_comp Gamma_include (@Gamma K V W I e he).
(** Source for [Gamma_AE]: Federer (1969), 1.4.5, p. 20, natural Hom-tensor
    isomorphism and dual-basis formula for Gamma. In words: For
    finite-dimensional V, the inverse Gamma of the Hom-tensor identification
    sends f to the sum of each dual basic covector tensored with the image
    of its basis vector. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Gamma_AE f : Gamma_A f = \sum_i @A_pure K h2 V W 1
  (one_form (dual_basis he i)) (exterior_first_inclusion W (f (e i))).
Proof.
change (Gamma_include (@Gamma K V W I e he f) = \sum_i @A_pure K h2 V W 1 (one_form (dual_basis he i)) (exterior_first_inclusion W (f (e i)))).
rewrite GammaE linear_sum; apply: eq_bigr => i _; exact: Gamma_includeE.
Qed.
End GammaInAlgebra.

(** Federer 1.4.5, the definition of trace: tensor evaluation restricts
    to a linear functional on A, with exactly the displayed pairing. *)
Section Trace.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Local Notation U := (alternating_unital_algebra h2 V (scalar_algebra K)).
Local Notation E := (exterior_algebra V).
(** Source for [trace_pair]: Federer (1969), 1.4.5, p. 20, definition of
    trace by its value on a homogeneous pure tensor. In words: Trace is the
    linear functional on the diagonal algebra taking a covector tensored
    with an m-vector to their evaluation pairing. Definition or construction
    used to formalise this passage. *)
Definition trace_pair (phi : U) (xi : E) : K^o := phi xi.
(** Source for [trace_pair_bilinear]: Federer (1969), 1.4.5, p. 20,
    definition of trace by its value on a homogeneous pure tensor. In words:
    Trace is the linear functional on the diagonal algebra taking a covector
    tensored with an m-vector to their evaluation pairing. Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma trace_pair_bilinear : bilinear trace_pair.
Proof.
split.
- move=> xi c phi psi; by rewrite /trace_pair hom_finite_addE hom_finite_scaleE.
- move=> phi; exact: hom_linear.
Qed.
(** Source for [trace_tensor]: Federer (1969), 1.4.5, p. 20, definition of
    trace by its value on a homogeneous pure tensor. In words: Trace is the
    linear functional on the diagonal algebra taking a covector tensored
    with an m-vector to their evaluation pairing. Definition or construction
    used to formalise this passage. *)
Definition trace_tensor : {linear tensor_space U E -> K^o} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift trace_pair_bilinear) _.
(** Source for [trace_tensorE]: Federer (1969), 1.4.5, p. 20, definition of
    trace by its value on a homogeneous pure tensor. In words: Trace is the
    linear functional on the diagonal algebra taking a covector tensored
    with an m-vector to their evaluation pairing. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma trace_tensorE phi xi : trace_tensor (tensor_inj phi xi) = phi xi.
Proof. exact: tensor_liftE. Qed.
(** Source for [trace]: Federer (1969), 1.4.5, p. 20, definition of trace by
    its value on a homogeneous pure tensor. In words: Trace is the linear
    functional on the diagonal algebra taking a covector tensored with an
    m-vector to their evaluation pairing. Definition or construction used to
    formalise this passage. *)
Definition trace : {linear A h2 V V -> K^o} := linear_comp trace_tensor (@A_include K h2 V V).
(** Source for [trace_pure]: Federer (1969), 1.4.5, p. 20, definition of
    trace by its value on a homogeneous pure tensor. In words: Trace is the
    linear functional on the diagonal algebra taking a covector tensored
    with an m-vector to their evaluation pairing. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Theorem trace_pure m (phi : A_m V K^o m) (xi : exterior_power V m) :
  trace (@A_pure K h2 V V m phi xi) = pairing xi phi.
Proof.
change (trace_tensor (tensor_inj (form_include phi) (component_val xi)) = pairing xi phi).
by rewrite trace_tensorE form_includeE /pairing form_to_homE.
Qed.
(** Source for [trace_Gamma_include]: Federer (1969), 1.4.5, p. 20,
    definition of trace by its value on a homogeneous pure tensor. In words:
    Trace is the linear functional on the diagonal algebra taking a covector
    tensored with an m-vector to their evaluation pairing. Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma trace_Gamma_include phi v : trace (@Gamma_include K h2 V V (tensor_inj phi v)) = one_hom phi v.
Proof.
rewrite Gamma_includeE trace_pure /pairing form_to_homE.
change (form_extension phi (exterior_degree 1 (exterior_generator v)) = one_hom phi v).
rewrite exterior_generator_homogeneous.
change (form_extension phi (exterior_word [tuple v]) = one_hom phi v).
by rewrite form_extensionE form_wordsE one_homE.
Qed.
Variable I : finType.
Variable e : I -> V.
Hypothesis he : is_basis e.
(** Federer 1.4.5: henceforth trace(Gamma(f)) is abbreviated trace(f).
    The separate Rocq name trace_Hom makes the two domains explicit. *)
(** Source for [trace_Hom]: Federer (1969), 1.4.5, p. 21, sentence
    abbreviating trace[Gamma(f)]. In words: The trace of an endomorphism
    abbreviates the trace of its image under Gamma. Definition or
    construction used to formalise this passage. *)
Definition trace_Hom : {linear Hom V V -> K^o} := linear_comp trace (@Gamma_A K h2 V V I e he).
(** Source for [trace_HomE]: Federer (1969), 1.4.5, p. 21, sentence
    abbreviating trace[Gamma(f)]. In words: The trace of an endomorphism
    abbreviates the trace of its image under Gamma. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Theorem trace_HomE f : trace_Hom f = \sum_i dual_basis he i (f (e i)).
Proof.
change (trace (@Gamma_A K h2 V V I e he f) = \sum_i dual_basis he i (f (e i))).
rewrite Gamma_AE linear_sum; apply: eq_bigr => i _.
rewrite trace_pure /pairing /one_form hom_to_formK hom_of_linearE.
exact (congr1 (dual_basis he i) (@exterior_first_inclusionK K V (f (e i)))).
Qed.
End Trace.
