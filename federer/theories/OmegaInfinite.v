(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import OmegaConstruction OmegaComponents OmegaNaturality
  InfiniteSequence CountableRetraction BlockCovector CountableNonSurjectivity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4: restrict Omega to degree m in its naturality identity. *)
Section Naturality.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V V' : lmodType K.
Variable f : {linear V -> V'}.
Local Notation d := (GRing.Linear.clone _ _ _ _ (@Hom_dual K V V' (scalar_algebra K) f) _).
(** Source for [Omega_m_natural]: Federer (1969), 1.4.4, pp. 19-20,
    canonical map Omega, together with the dual maps of 1.4.1. In words: The
    canonical map from exterior products of covectors to alternating forms
    is compatible with pullback Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Omega_m_natural m (x : exterior_power (Hom V' K^o) m) :
  A_m_dual f (Omega_m h2 x) = Omega_m h2 (exterior_power_map d m x).
Proof.
apply: (can_inj (@form_includeK K V K^o m)).
rewrite -A_star_dual_include !Omega_m_include.
exact (@Omega_W_natural K h2 V V' (scalar_algebra K) f (@mulrC K) (component_val x)).
Qed.
End Naturality.

(** Source for [A_m_dual_retraction]: Federer (1969), 1.4.4, pp. 19-20,
    canonical map Omega, together with the dual maps of 1.4.1. In words: The
    canonical map from exterior products of covectors to alternating forms
    is compatible with pullback Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma A_m_dual_retraction (K : fieldType) (V W Z : lmodType K)
    (i : {linear V -> W}) (q : {linear W -> V}) : cancel i q ->
  forall m (phi : A_m V Z m), A_m_dual i (A_m_dual q phi) = phi.
Proof.
move=> hi m phi; apply: form_ext => t; rewrite !A_m_dualE.
congr (phi _); apply: eq_from_tnth => j; by rewrite !tnth_map hi.
Qed.

(** Federer 1.4.4, the infinite-dimensional assertion in full: for
    each degree at least two, a covector is absent from the image of
    the whole algebra map Omega. The countable construction is
    transported by a proved linear retraction. *)
Section Infinite.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Hypothesis hinf : infinite_dimensional V.
Local Notation N := (Choice.clone nat _).
Local Notation F := (GRing.Lmodule.clone K (free_vector K N) _).
Local Notation i := (countable_inclusion hinf).
Local Notation q := (countable_retraction hinf).
(** Source for [infinite_block_covector]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition infinite_block_covector m : A_m V K^o m.+2 := A_m_dual q (@block_covector K h2 m.+2).
(** Source for [infinite_block_not_in_component_image]: Federer (1969),
    1.4.4, p. 20, infinite-dimensional assertion immediately before the
    parenthesis. In words: In infinite dimension, for every degree m at
    least two there are m-covectors outside the image of Omega. Supporting
    lemma for this passage; not separately stated in the book. *)
Theorem infinite_block_not_in_component_image m :
  ~ exists x : exterior_power (Hom V K^o) m.+2, Omega_m h2 x = infinite_block_covector m.
Proof.
move=> [x hx]; apply: (@block_covector_not_in_image K h2 m).
pose d : {linear Hom V K^o -> Hom F K^o} :=
  GRing.Linear.clone _ _ _ _ (@Hom_dual K F V (scalar_algebra K) i) _.
exists (exterior_power_map d m.+2 x).
rewrite -(Omega_m_natural h2 i) hx /infinite_block_covector.
exact (@A_m_dual_retraction K F V K^o i q (countable_retractionK hinf) m.+2 (@block_covector K h2 m.+2)).
Qed.
(** Source for [infinite_block_not_in_image]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Theorem infinite_block_not_in_image m :
  ~ exists x : exterior_space (Hom V K^o), Omega h2 V x = form_include (infinite_block_covector m).
Proof.
move=> [x hx]; apply: (@infinite_block_not_in_component_image m).
exists (component (exterior_grading (Hom V K^o)) m.+2 x).
by rewrite Omega_component hx form_includeK.
Qed.
(** Source for [Omega_infinite_missing_degree]: Federer (1969), 1.4.4, p.
    20, infinite-dimensional assertion immediately before the parenthesis.
    In words: In infinite dimension, for every degree m at least two there
    are m-covectors outside the image of Omega. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Theorem Omega_infinite_missing_degree m : (2 <= m)%N ->
  exists phi : A_m V K^o m, ~ exists x, Omega h2 V x = form_include phi.
Proof.
case: m => [|[|m]] // _; exists (infinite_block_covector m).
exact: infinite_block_not_in_image.
Qed.
End Infinite.
