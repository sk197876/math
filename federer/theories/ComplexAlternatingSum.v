(** Federer (1969), 1.6.6, p. 26: A_C^*(V,W), for arbitrary complex
    coefficient space W. The direct-sum specification uses complex
    multilinearity of the homogeneous components. The finite decomposition
    and uniqueness are inherited from the independently formalised
    alternating direct sum, with scalar restriction checked. Source context
    are recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates AlternatingSum ScalarRestriction
  ComplexAlternatingForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Sum.
Variables R C : fieldType.
Variable embed : {rmorphism R -> C}.
Variables V W : lmodType C.
Local Notation VR := (restricted_space embed V).
Local Notation WR := (restricted_space embed W).
Local Notation A := (A_star VR WR).

(** Source for [complex_alternating_sum]: Federer 1.6.6,
    p. 26, direct-sum definition of A_C^*(V,W). The condition is
    imposed on each component; finite support is part of A^*(V,W). *)
Definition complex_alternating_sum (a : A) := forall m,
  @complex_multilinear_form R C embed V W m (form_component m a).

(** Source for [complex_sum_component]: Federer 1.6.6,
    p. 26, the direct-sum components A_C^m(V,W). Each component
    is an actual alternating form defined over C. *)
Definition complex_sum_component (a : A) (ha : complex_alternating_sum a) m : A_m V W m :=
  @complex_form R C embed V W m (form_component m a) (ha m).

(** Source for [complex_sum_componentE]: Federer 1.6.6,
    p. 26, direct-sum components. Restriction recovers the original
    real homogeneous component exactly. *)
Lemma complex_sum_componentE a ha m :
  restrict_form embed (@complex_sum_component a ha m) = form_component m a.
Proof. exact: restrict_complex_form. Qed.

(** Source for [complex_alternating_sum_decomposition]: Federer
    1.6.6, p. 26, the direct-sum display. Every member has a finite
    decomposition into its included complex homogeneous components. *)
Theorem complex_alternating_sum_decomposition a (ha : complex_alternating_sum a) :
  exists N, a = \sum_(j < N) form_include (restrict_form embed (@complex_sum_component a ha j)).
Proof.
have [N hN] := alternating_sum_decomposition a; exists N.
apply: (eq_trans hN); apply: eq_bigr => j _; by rewrite complex_sum_componentE.
Qed.

(** Source for [complex_alternating_sum_ext]: Federer 1.6.6,
    p. 26, directness of the sum. Equality of every complex component
    determines the full form uniquely. *)
Theorem complex_alternating_sum_ext a b (ha : complex_alternating_sum a)
  (hb : complex_alternating_sum b) :
  (forall m, @complex_sum_component a ha m = @complex_sum_component b hb m) -> a = b.
Proof.
move=> h; apply: alternating_sum_ext => m.
by rewrite -(complex_sum_componentE ha m) -(complex_sum_componentE hb m) h.
Qed.
End Sum.
