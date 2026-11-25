(** Federer (1969), 1.7.6, p. 33: trace(adjoint f) = trace(f). We use the
    intrinsic trace from 1.4.5, change to an orthonormal basis, and compare
    its diagonal entries by the adjoint equation. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP AdjointUP LinearBasis
  GramSchmidt OrthonormalisationUP OrthonormalFamilies OrthonormalParseval
  TraceDefinition GammaIntrinsic Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [adjoint_trace]: Federer 1.7.6, p. 33,
    an endomorphism and its adjoint have equal traces, including
    the empty trace in dimension zero. *)
Theorem adjoint_trace (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b)
    (f a : {linear V -> V}) (ha : is_adjoint B B f a) :
  @trace_Hom R h2 V (Finite.clone 'I_n _) b hb (hom_of_linear a) =
  @trace_Hom R h2 V (Finite.clone 'I_n _) b hb (hom_of_linear f).
Proof.
have [e [he ho]] := orthonormal_basis_exists hB hb.
have horth := orthonormalisation_orthonormal ho.
rewrite (@trace_basis_independent R h2 V (Finite.clone 'I_n _) (Finite.clone 'I_n _)
  b e hb he (hom_of_linear a)).
rewrite (@trace_basis_independent R h2 V (Finite.clone 'I_n _) (Finite.clone 'I_n _)
  b e hb he (hom_of_linear f)).
rewrite !trace_HomE; apply: eq_bigr => i _.
rewrite !(@orthonormal_basis_inner_coordinate R V B hB
  (Finite.clone 'I_n _) e horth he).
change (B (a (e i)) (e i) = B (f (e i)) (e i)).
by rewrite (inner_symmetric hB) ha.
Qed.
