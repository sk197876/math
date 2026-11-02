(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import GammaPower TraceDefinition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5: traces on the higher exterior powers agree with
    the trace of their images under Gamma in the diagonal algebra. *)
Section TracePower.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation omega := (fun i => one_form (dual_basis he i)).
(** Source for [trace_Gamma_power]: Federer (1969), 1.4.5, p. 21, sentence
    abbreviating trace[Gamma(f)]. In words: The trace of an endomorphism
    abbreviates the trace of its image under Gamma. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Lemma trace_Gamma_power m f :
  trace h2 V (@Gamma_power_A K h2 V V n e he m f) =
  @trace_Hom K h2 (exterior_power V m) (Finite.clone (Lambda n m) _)
    (@finite_e_lambda K n V e m) (finite_e_lambda_basis he h2 m) f.
Proof.
rewrite Gamma_power_AE linear_sum trace_HomE.
apply: eq_bigr => lambda _.
by rewrite trace_pure -(Gamma_coordinate h2 he) /pairing hom_to_formK.
Qed.
(** Source for [trace_Gamma_powerE]: Federer (1969), 1.4.5, p. 21, sentence
    abbreviating trace[Gamma(f)]. In words: The trace of an endomorphism
    abbreviates the trace of its image under Gamma. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma trace_Gamma_powerE m f :
  trace h2 V (@Gamma_power_A K h2 V V n e he m f) =
    \sum_(lambda : Lambda n m) pairing (f (e_lambda e (val lambda)))
      (omega_lambda h2 omega lambda).
Proof.
rewrite Gamma_power_AE linear_sum; apply: eq_bigr => lambda _.
exact: trace_pure.
Qed.
(** Federer 1.4.5: the top exterior power is a line; the scalar by
    which its endomorphism acts is the determinant defined in 1.3.4. *)
(** Source for [trace_top_power]: Federer (1969), 1.4.5, p. 21, first
    display beginning Moreover. In words: The trace of the top divided power
    of Gamma(f), equivalently of Gamma of the top exterior map, is det(f).
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Theorem trace_top_power (f : {linear V -> V}) :
  trace h2 V (@Gamma_power_A K h2 V V n e he n
    (hom_of_linear (exterior_power_map f n))) = det h2 he f.
Proof.
rewrite trace_Gamma_powerE.
rewrite (big_pred1 (Lambda_top n)); last by move=> lambda; rewrite /pred1 /= (Lambda_top_unique lambda) eqxx.
rewrite hom_of_linearE (detE h2 he) (bilZl (@pairing_bilinear K V K^o n)).
rewrite (pairing_e_omega h2 (Gamma_dualE he)) eqxx.
change ((det h2 he f : K) * 1 = det h2 he f); exact: mulr1.
Qed.
End TracePower.
