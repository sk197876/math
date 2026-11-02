(** Federer (1969), 1.7.9, p. 35, first displayed computation: the product
    of f and g is the trace of the adjoint of f composed with g. We retain
    the latter generality. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP HomInner HomInnerCoordinates
  AdjointUP Adjoint LinearBasis Hom TensorUP GammaIntrinsic TraceDefinition
  GramSchmidt OrthonormalisationUP OrthonormalParseval.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [hom_inner_adjoint_trace]: Federer 1.7.9, p. 35,
    equality of the inner product of f and g with trace(a composed
    with g), for any a satisfying the adjoint equation for f. *)
Theorem hom_inner_adjoint_trace (R : rcfType) (h2 : (1+1 : R) != 0)
    (V W : lmodType R) (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b)
    (f g : Hom V W) (a : {linear W -> V})
    (ha : is_adjoint B C (hom_as_linear f) a) :
  hom_inner hB hC hb f g =
  @trace_Hom R h2 V (Finite.clone 'I_n _) b hb
    (hom_of_linear (linear_comp a (hom_as_linear g))).
Proof.
have [e [he ho]] := orthonormal_basis_exists hB hb.
have horth := orthonormalisation_orthonormal ho.
rewrite (@hom_inner_orthonormal_sum R V W B C hB hC n b hb n e he horth f g).
rewrite (@trace_basis_independent R h2 V (Finite.clone 'I_n _) (Finite.clone 'I_n _)
  b e hb he).
rewrite trace_HomE; apply: eq_bigr => i _.
rewrite (@orthonormal_basis_inner_coordinate R V B hB
  (Finite.clone 'I_n _) e horth he).
change (C (f (e i)) (g (e i)) = B (a (g (e i))) (e i)).
rewrite (inner_symmetric hB).
exact: esym (ha (e i) (g (e i))).
Qed.

(** Source for [hom_inner_trace]: Federer 1.7.9, p. 35,
    the trace formula with the canonical adjoint of f. *)
Theorem hom_inner_trace (R : rcfType) (h2 : (1+1 : R) != 0)
    (V W : lmodType R) (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b) (f g : Hom V W) :
  hom_inner hB hC hb f g =
  @trace_Hom R h2 V (Finite.clone 'I_n _) b hb
    (hom_of_linear (linear_comp (inner_adjoint hB hC hb (hom_as_linear f)) (hom_as_linear g))).
Proof. exact: hom_inner_adjoint_trace (inner_adjointP hB hC hb (hom_as_linear f)). Qed.
