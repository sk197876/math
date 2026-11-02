(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import TraceAlgebra AlgebraPowers SelectionPowers GammaProducts
  GammaPower TraceDefinition TracePower.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5, divided m-th power. The factorial identity is
    established first without division. Federer's displayed formula
    follows when m! is nonzero, in particular over the real field. *)
Section DividedPowers.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation D := (A h2 V W).
Local Notation omega := (fun i => one_form (dual_basis he i)).
Local Notation G := (@Gamma_A K h2 V W (Finite.clone 'I_n _) e he).
(** Source for [Gamma_power_factorial]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Theorem Gamma_power_factorial (f : Hom V W) m :
  @algebra_power K D (G f) m = (m`!%:R : K) *:
    @Gamma_power_A K h2 V W n e he m
      (hom_of_linear (exterior_power_map (hom_as_linear f) m)).
Proof.
rewrite Gamma_AE.
change (@algebra_power K D (\sum_i Gamma_term h2 (omega i) (f (e i))) m =
  (m`!%:R : K) *: @Gamma_power_A K h2 V W n e he m
    (hom_of_linear (exterior_power_map (hom_as_linear f) m))).
rewrite (@square_zero_Lambda_power K D (@A_commutative K h2 V W) n
  (fun i => Gamma_term h2 (omega i) (f (e i)))
  (fun i => @Gamma_term_square K h2 V W (omega i) (f (e i))) m).
rewrite Gamma_power_AE; congr (_ *: _); apply: eq_bigr => lambda _.
exact: Gamma_Lambda_product.
Qed.
(** Source for [Gamma_divided_power]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Theorem Gamma_divided_power (f : Hom V W) m : (m`!%:R : K) != 0 ->
  (m`!%:R : K)^-1 *: @algebra_power K D (G f) m =
    @Gamma_power_A K h2 V W n e he m
      (hom_of_linear (exterior_power_map (hom_as_linear f) m)).
Proof. move=> hm; by rewrite Gamma_power_factorial scalerA mulVf // scale1r. Qed.
(** Source for [Gamma_divided_power_formula]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Theorem Gamma_divided_power_formula (f : Hom V W) m : (m`!%:R : K) != 0 ->
  (m`!%:R : K)^-1 *: @algebra_power K D (G f) m =
    \sum_(lambda : Lambda n m) A_pure h2 (omega_lambda h2 omega lambda)
      (exterior_power_map (hom_as_linear f) m (e_lambda e (val lambda))).
Proof. move=> hm; by rewrite (Gamma_divided_power f hm) Gamma_power_AE. Qed.
End DividedPowers.

(** Source for [characteristic_zero_factorial]: Federer (1969), 1.4.5, p.
    20, divided-power display and following natural isomorphisms. In words:
    The divided m-th power of Gamma(f) is the sum of omega_lambda tensored
    with the m-th exterior image of e_lambda, and equals Gamma of that
    exterior map. Supporting lemma for this passage; not separately stated
    in the book. *)
Lemma characteristic_zero_factorial (K : fieldType) : [pchar K] =i pred0 ->
  forall m, (m`!%:R : K) != 0.
Proof. move/pcharf0P=> h m; by rewrite h -lt0n fact_gt0. Qed.

(** Federer 1.4.5, first display on page 21: the complete equality
    trace(Gamma(f)^n/n!) = trace(Gamma(exterior_power f)) = det(f). *)
(** Source for [trace_divided_top_power]: Federer (1969), 1.4.5, p. 21,
    first display beginning Moreover. In words: The trace of the top divided
    power of Gamma(f), equivalently of Gamma of the top exterior map, is
    det(f). Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem trace_divided_top_power (K : fieldType) (h2 : (1+1 : K) != 0)
    (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
    (f : Hom V V) : (n`!%:R : K) != 0 ->
  trace h2 V ((n`!%:R : K)^-1 *: @algebra_power K (A h2 V V)
    (@Gamma_A K h2 V V (Finite.clone 'I_n _) e he f) n) = det h2 he (hom_as_linear f).
Proof. move=> hn; by rewrite (Gamma_divided_power h2 he f hn) trace_top_power. Qed.
