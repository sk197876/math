(** Federer (1969), 1.7.9, p. 35: positivity is checked on finite
    orthonormal families containing the factors of a tensor. No basis of an
    infinite-dimensional ambient space is chosen. Empty families and the
    zero tensor are included. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP OrthonormalFamilies GramSchmidt
  OrthonormalisationUP FiniteSpans FiniteIndependence TensorUP TensorProduct
  TensorSpan BilinearDoubleExpansion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_orthonormal_span]: Federer 1.7.9,
    p. 35, supporting reduction: any finite list of vectors
    lies in the span of a finite orthonormal family. *)
Lemma finite_orthonormal_span (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (s : seq V) :
  exists n (e : 'I_n -> V), orthonormal_family B e /\
    forall v, v \in s -> in_finite_span e v.
Proof.
have [n [u [hu hs]]] := finite_independent_span s.
have [e he] := @gram_schmidt_exists R V B hB n u hu.
exists n, e; split; first exact: orthonormalisation_orthonormal he.
move=> v hv; exact: (proj1 (@orthonormalisation_span R V B n u e he v)) (hs v hv).
Qed.

(** Source for [finite_families_tensor_expansion]: Federer 1.7.9,
    p. 35, supporting bilinear expansion: tensors with factors in
    two finite spans are combinations of their pairwise pure tensors. *)
Lemma finite_families_tensor_expansion (R : fieldType) (V W : lmodType R)
    m k (e : 'I_m -> V) (f : 'I_k -> W) (s : seq (R * (V * W))) :
  (forall t, t \in s -> in_finite_span e t.2.1 /\ in_finite_span f t.2.2) ->
  exists c : ('I_m * 'I_k)%type -> R,
    (\sum_(t <- s) t.1 *: tensor_inj t.2.1 t.2.2) =
      \sum_ij c ij *: tensor_inj (e ij.1) (f ij.2).
Proof.
elim: s => [|t s ih] hs.
- exists (fun _ => 0); rewrite big_nil; symmetry; apply: big1 => ij _; exact: scale0r.
- have [[a ha] [b hb]] := hs t (mem_head t s).
  have hs' u (hu : u \in s) : in_finite_span e u.2.1 /\ in_finite_span f u.2.2.
    apply: hs; by rewrite in_cons hu orbT.
  have [c hc] := ih hs'.
  exists (fun ij => t.1 * (a ij.1 * b ij.2) + c ij).
  rewrite big_cons ha hb (bilinear_double_expansion (tensor_inj_bilinear V W))
    pair_bigA hc scaler_sumr -big_split.
  apply: eq_bigr => [[i j]] _; by rewrite scalerDl scalerA.
Qed.

(** Source for [tensor_finite_orthonormal_expansion]: Federer
    1.7.9, p. 35, the finite orthonormal expansion used to
    prove positive definiteness in arbitrary ambient dimensions. *)
Theorem tensor_finite_orthonormal_expansion (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C) (x : tensor_space V W) :
  exists m k (e : 'I_m -> V) (f : 'I_k -> W)
    (c : ('I_m * 'I_k)%type -> R),
    orthonormal_family B e /\ orthonormal_family C f /\
      x = \sum_ij c ij *: tensor_inj (e ij.1) (f ij.2).
Proof.
have [s hx] := tensor_span x.
have [m [e [he hse]]] := finite_orthonormal_span hB [seq t.2.1 | t <- s].
have [k [f [hf hsf]]] := finite_orthonormal_span hC [seq t.2.2 | t <- s].
have hs t (ht : t \in s) : in_finite_span e t.2.1 /\ in_finite_span f t.2.2.
  split.
  - apply: hse; apply/mapP; by exists t.
  - apply: hsf; apply/mapP; by exists t.
have [c hc] := finite_families_tensor_expansion hs.
exists m, k, e, f, c; split=> //; split=> //; exact: eq_trans hx hc.
Qed.
