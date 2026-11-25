(** Federer (1969), 1.7.12, pp. 36-37: supporting trace equalities when the
    first formula is applied to f+adjoint(f). These follow from the adjoint
    trace identity of 1.7.6, p. 33, and reversal of composition in 1.7.4, p.
    30. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP AdjointUP AdjointLaws AdjointTrace
  TraceDefinition LinearBasis Hom TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [adjoint_hom_trace]: Federer 1.7.12,
    pp. 36-37, supporting rewriting of trace(adjoint f) as trace(f)
    in the Hom interface used by the second identity. *)
Lemma adjoint_hom_trace (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (f a : Hom V V)
    (ha : is_adjoint B B (hom_as_linear f) (hom_as_linear a)) :
  @trace_Hom R h2 V (Finite.clone 'I_n _) e he a =
    @trace_Hom R h2 V (Finite.clone 'I_n _) e he f.
Proof.
have hh := @adjoint_trace R h2 V B hB n e he (hom_as_linear f) (hom_as_linear a) ha.
by rewrite !hom_of_asK in hh.
Qed.

(** Source for [adjoint_square_trace]: Federer 1.7.12,
    pp. 36-37, supporting equality trace(adjoint(f) composed with adjoint(f))=
    trace(f composed with f), since these two maps are adjoints. *)
Lemma adjoint_square_trace (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (f a : Hom V V)
    (ha : is_adjoint B B (hom_as_linear f) (hom_as_linear a)) :
  @trace_Hom R h2 V (Finite.clone 'I_n _) e he (hom_comp a a) =
    @trace_Hom R h2 V (Finite.clone 'I_n _) e he (hom_comp f f).
Proof.
have haa := @adjoint_composition R V V V B B B
  (hom_as_linear f) (hom_as_linear f) (hom_as_linear a) (hom_as_linear a) ha ha.
exact (@adjoint_trace R h2 V B hB n e he
  (linear_comp (hom_as_linear f) (hom_as_linear f))
  (linear_comp (hom_as_linear a) (hom_as_linear a)) haa).
Qed.

(** Source for [double_trace_scalar_identity]: Federer 1.7.12,
    pp. 36-37, supporting scalar simplification after substituting
    the adjoint and cyclic trace identities into the first formula. *)
Lemma double_trace_scalar_identity (R : fieldType) (t u v : R) :
  (t+t)^+2 - (u+v+(v+u)) = (2 : R) * ((2 : R) * t^+2-u-v).
Proof.
have ht : t+t = (2 : R)*t by rewrite mulr_natl mulr2n.
have hu : u+v+(v+u) = (2 : R)*(u+v).
  by rewrite [v+u]addrC mulr_natl mulr2n.
rewrite ht hu exprMn expr2 -mulrA -mulrBr.
by rewrite opprD addrA.
Qed.
