(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import OmegaConstruction OmegaNaturality ExteriorFiniteSupport
  FiniteEvaluation FiniteEvaluationMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4, infinite-dimensional assertion: every element in the
    image of Omega factors through finitely many linear functionals. This
    implies finite rank after fixing all but one argument. *)
Section Reconstruction.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Variable omega : 'I_n -> Hom V K^o.
(** Source for [covector_analysis]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition covector_analysis (v : V) : coordinate_space K n := [ffun i => omega i v].
(** Source for [covector_analysis_linear]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma covector_analysis_linear : linear covector_analysis.
Proof. move=> c v w; apply/ffunP=> i; rewrite /covector_analysis !ffunE; exact: hom_linear. Qed.
HB.instance Definition _ := GRing.isLinear.Build K V (coordinate_space K n)
  *:%R covector_analysis covector_analysis_linear.
(** Source for [reconstruction_map]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition reconstruction_map : {linear V -> V} :=
  linear_comp (point_synthesis e) (GRing.Linear.clone _ _ _ _ covector_analysis _).
(** Source for [point_synthesis_sum]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma point_synthesis_sum z : point_synthesis e z = \sum_i (z i : K) *: e i.
Proof.
change (basis_synthesis e (coordinate_to_free z) = \sum_i (z i : K) *: e i).
rewrite basis_synthesis_finiteE; apply: eq_bigr => i _; by rewrite coordinate_to_freeE.
Qed.
(** Source for [Hom_dual_reconstruction]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma Hom_dual_reconstruction (a : Hom V K^o) :
  @Hom_dual K V V (scalar_algebra K) reconstruction_map a = evaluation_reconstruction e omega a.
Proof.
apply: hom_ext => v; rewrite Hom_dualE evaluation_reconstructionE.
change (a (point_synthesis e (covector_analysis v)) = \sum_i a (e i)*omega i v).
rewrite point_synthesis_sum linear_sum.
change ((\sum_i a ((covector_analysis v i : K) *: e i)) = \sum_i a (e i)*omega i v).
apply: eq_bigr => i _; rewrite (linZ (hom_linear a)) /covector_analysis ffunE.
change (omega i v * a (e i) = a (e i)*omega i v); exact: mulrC.
Qed.
End Reconstruction.

Section FiniteRank.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
(** Source for [Omega_finite_rank_pullback]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Theorem Omega_finite_rank_pullback (x : exterior_space (Hom V K^o)) :
  exists n (e : 'I_n -> V) (omega : 'I_n -> Hom V K^o),
    Omega h2 V x = A_star_dual (reconstruction_map e omega) (Omega h2 V x).
Proof.
have [s hs] := exterior_finite_support x.
have [n [e [omega he]]] := finite_evaluation_reconstruction s.
exists n, e, omega.
pose f := reconstruction_map e omega.
pose d : {linear Hom V K^o -> Hom V K^o} :=
  GRing.Linear.clone _ _ _ _ (@Hom_dual K V V (scalar_algebra K) f) _.
have hx : exterior_algebra_map d x = x.
  apply: hs => a ha; change (@Hom_dual K V V (scalar_algebra K) f a = a).
  rewrite /f Hom_dual_reconstruction; exact: he ha.
have hn := @Omega_W_natural K h2 V V (scalar_algebra K) f (@mulrC K) x.
change (A_star_dual f (Omega h2 V x) = Omega h2 V (exterior_algebra_map d x)) in hn.
by rewrite hx in hn; symmetry.
Qed.
(** Source for [Omega_m_finite_rank_pullback]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Theorem Omega_m_finite_rank_pullback m (x : exterior_power (Hom V K^o) m) :
  exists n (e : 'I_n -> V) (omega : 'I_n -> Hom V K^o),
    Omega_m h2 x = A_m_dual (reconstruction_map e omega) (Omega_m h2 x).
Proof.
have [n [e [omega he]]] := Omega_finite_rank_pullback (component_val x).
exists n, e, omega.
have h := congr1 (@form_component K V K^o m) he.
by rewrite A_star_dual_component in h.
Qed.
End FiniteRank.
