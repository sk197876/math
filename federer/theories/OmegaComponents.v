(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import OneFormIdentification OmegaConstruction OmegaFinite.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4: the graded map is injective precisely when its
    restrictions are injective; this makes the degree-by-degree
    argument in the book an assertion about the whole algebra. *)
Section Components.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Local Notation G := (exterior_grading (Hom V K^o)).
(** Source for [Omega_component]: Federer (1969), 1.4.4, p. 19, monomorphism
    assertion and basis argument. In words: Omega is injective because it
    takes exterior products of independent covectors to their independent
    alternating products. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Omega_component m x :
  Omega_m h2 (component G m x) = form_component m (Omega h2 V x).
Proof.
apply: (can_inj (@form_includeK K V K^o m)).
rewrite Omega_m_include form_componentK.
exact (@graded_map_projection K (exterior_space (Hom V K^o)) (A_star V K^o)
  G (A_star_grading V K^o) (Omega h2 V) (@Omega_graded K h2 V) m x).
Qed.
(** Source for [Omega_injective_from_components]: Federer (1969), 1.4.4, p.
    19, monomorphism assertion and basis argument. In words: Omega is
    injective because it takes exterior products of independent covectors to
    their independent alternating products. Supporting lemma for this
    passage; not separately stated in the book. *)
Theorem Omega_injective_from_components :
  (forall m, injective (@Omega_m K h2 V m)) -> injective (Omega h2 V).
Proof.
move=> hinj.
have hker x : Omega h2 V x = 0 -> x = 0.
  move=> hx; have [N hN] := grade_finite G x; rewrite hN.
  apply: big1 => i _.
  have hc : component G i x = 0.
    apply: (hinj i); rewrite Omega_component hx !linear0; by [].
  exact (congr1 (@component_val K _ G i) hc).
move=> x y hxy; apply/eqP; rewrite -subr_eq0; apply/eqP; apply: hker.
by rewrite linearB hxy subrr.
Qed.
End Components.

(** Source for [Omega_finite_injective]: Federer (1969), 1.4.4, p. 20,
    opening finite-dimensional epimorphism assertion. In words: When V is
    finite dimensional, Omega is surjective: in each degree the source and
    target have the same binomial dimension. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Theorem Omega_finite_injective (K : fieldType) (h2 : (1+1 : K) != 0)
    (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e) : injective (Omega h2 V).
Proof.
apply: Omega_injective_from_components => m.
exact (@Omega_m_finite_injective K h2 V n e he m).
Qed.
