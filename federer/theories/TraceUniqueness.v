(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import TraceAlgebra TraceComponents TraceDefinition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5: the prescribed values on homogeneous pure tensors
    determine trace uniquely on the entire direct sum A. *)
Section TraceUniqueness.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Variable Z : lmodType K.
Local Notation D := (A h2 V W).
(** Source for [A_linear_ext]: Federer (1969), 1.4.5, p. 20, definition of
    trace by its value on a homogeneous pure tensor. In words: Trace is the
    linear functional on the diagonal algebra taking a covector tensored
    with an m-vector to their evaluation pairing. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Theorem A_linear_ext (f g : {linear D -> Z}) :
  (forall m phi xi, f (@A_pure K h2 V W m phi xi) = g (@A_pure K h2 V W m phi xi)) -> f =1 g.
Proof.
move=> hp x; have [N ->] := @A_direct_sum K h2 V W x.
rewrite !linear_sum; apply: eq_bigr => i _.
apply (@tensor_ext K (A_m V K^o i) (exterior_power W i)
  (tensor_space (A_m V K^o i) (exterior_power W i)) (@tensor_inj K (A_m V K^o i) (exterior_power W i))
  (tensor_exists (A_m V K^o i) (exterior_power W i)) Z
  (linear_comp f (@A_component K h2 V W i)) (linear_comp g (@A_component K h2 V W i))).
move=> phi xi.
change (f (@A_component K h2 V W i (tensor_inj phi xi)) = g (@A_component K h2 V W i (tensor_inj phi xi))).
by rewrite A_componentE hp.
Qed.
End TraceUniqueness.
(** Source for [trace_unique]: Federer (1969), 1.4.5, p. 20, definition of
    trace by its value on a homogeneous pure tensor. In words: Trace is the
    linear functional on the diagonal algebra taking a covector tensored
    with an m-vector to their evaluation pairing. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Theorem trace_unique (K : fieldType) (h2 : (1+1 : K) != 0) (V : lmodType K)
    (t : {linear A h2 V V -> K^o}) :
  (forall m phi xi, t (@A_pure K h2 V V m phi xi) = pairing xi phi) -> t =1 trace h2 V.
Proof. move=> ht; apply: A_linear_ext => m phi xi; by rewrite ht trace_pure. Qed.
