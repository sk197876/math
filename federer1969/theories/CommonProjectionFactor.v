(** Federer (1969), 1.7.4, p. 31, last paragraph: common orthogonal factors
    of two orthogonal projections. The proof follows the book: embed the
    common target in the intersection of the adjoint images, then take
    adjoints. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ModuleQuotient SubspaceCarrier SubspaceSums
  AnnihilatorIntersection AnnihilatorDimension LinearRangeBasis
  IntersectionDimensionBound InnerProductUP InnerProductRestriction
  OrthogonalMaps OrthogonalEmbedding AdjointUP Adjoint AdjointLaws
  ProjectionCriteria ProjectionRange LinearBasis TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [common_projection_factor_from_embedding]:
    Federer 1.7.4, p. 31, last two sentences. An orthogonal copy
    of W3 in the intersection of the two adjoint images gives
    projections p and q with p composed with f equal to q composed
    with g, by taking adjoints of its two lifts. *)
Theorem common_projection_factor_from_embedding (R : rcfType)
    (V W1 W2 W3 : lmodType R)
    (B : V -> V -> R) (C1 : W1 -> W1 -> R)
    (C2 : W2 -> W2 -> R) (D : W3 -> W3 -> R)
    (hB : is_inner_product B) (hC1 : is_inner_product C1)
    (hC2 : is_inner_product C2) (hD : is_inner_product D)
    (f : {linear V -> W1}) (g : {linear V -> W2})
    (a : {linear W1 -> V}) (b : {linear W2 -> V})
    (hfa : is_adjoint B C1 f a) (hgb : is_adjoint B C2 g b)
    (hf : is_orthogonal_projection B C1 f)
    (hg : is_orthogonal_projection B C2 g)
    k (c : 'I_k -> W3) (hc : is_basis c)
    (r : {linear W3 -> V}) (hr : is_orthogonal_map D B r)
    (hra : forall z, range_subspace a (r z))
    (hrb : forall z, range_subspace b (r z)) :
  exists (p : {linear W1 -> W3}) (q : {linear W2 -> W3}),
    is_orthogonal_projection C1 D p /\ is_orthogonal_projection C2 D q /\
    forall x, p (f x) = q (g x).
Proof.
pose u := linear_comp f r; pose v := linear_comp g r.
have hau z : a (u z) = r z :=
  @projection_inverse_on_adjoint_range R V W1 B C1 hB hC1 f a hfa hf (r z) (hra z).
have hbv z : b (v z) = r z :=
  @projection_inverse_on_adjoint_range R V W2 B C2 hB hC2 g b hgb hg (r z) (hrb z).
have hao := proj1 (@projection_iff_adjoint_orthogonal R V W1 B C1 hB hC1 f a hfa) hf.
have hbo := proj1 (@projection_iff_adjoint_orthogonal R V W2 B C2 hB hC2 g b hgb) hg.
have hu : is_orthogonal_map D C1 u.
  move=> x y; by rewrite -(hao (u x) (u y)) !hau hr.
have hv : is_orthogonal_map D C2 v.
  move=> x y; by rewrite -(hbo (v x) (v y)) !hbv hr.
pose p := inner_adjoint hD hC1 hc u.
pose q := inner_adjoint hD hC2 hc v.
have hp := @inner_adjointP R W3 W1 D C1 hD hC1 k c hc u.
have hq := @inner_adjointP R W3 W2 D C2 hD hC2 k c hc v.
exists p, q; split; first by exists u; split.
split; first by exists v; split.
move=> x; apply: (@inner_vectors_ext R W3 D hD) => z.
rewrite hp hq.
have haf := @adjoint_reverse R V W1 B C1 hB hC1 f a hfa.
have hbg := @adjoint_reverse R V W2 B C2 hB hC2 g b hgb.
by rewrite haf hbg hau hbv.
Qed.

(** Source for [common_orthogonal_projection_factor]: Federer
    1.7.4, p. 31, final assertion. If dim W1 + dim W2 - dim V
    is at least dim W3, the projections have a common orthogonal
    factor onto W3. The hypothesis uses n+k <= m1+m2, avoiding
    truncated natural-number subtraction. Zero dimensions are included. *)
Theorem common_orthogonal_projection_factor (R : realType)
    (V W1 W2 W3 : lmodType R)
    (B : V -> V -> R) (C1 : W1 -> W1 -> R)
    (C2 : W2 -> W2 -> R) (D : W3 -> W3 -> R)
    (hB : is_inner_product B) (hC1 : is_inner_product C1)
    (hC2 : is_inner_product C2) (hD : is_inner_product D)
    n (e : 'I_n -> V) (he : is_basis e)
    m1 (e1 : 'I_m1 -> W1) (he1 : is_basis e1)
    m2 (e2 : 'I_m2 -> W2) (he2 : is_basis e2)
    k (e3 : 'I_k -> W3) (he3 : is_basis e3)
    (f : {linear V -> W1}) (g : {linear V -> W2})
    (hf : is_orthogonal_projection B C1 f)
    (hg : is_orthogonal_projection B C2 g)
    (hdim : (n+k <= m1+m2)%N) :
  exists (p : {linear W1 -> W3}) (q : {linear W2 -> W3}),
    is_orthogonal_projection C1 D p /\ is_orthogonal_projection C2 D q /\
    forall x, p (f x) = q (g x).
Proof.
have [a [ha haf]] := hf; have [b [hb hbg]] := hg.
have hfa := @adjoint_reverse R W1 V C1 B hC1 hB a f haf.
have hgb := @adjoint_reverse R W2 V C2 B hC2 hB b g hbg.
have hai := @orthogonal_map_injective R W1 V C1 B hC1 hB a ha.
have hbi := @orthogonal_map_injective R W2 V C2 B hC2 hB b hb.
have [a1 ha1] := @injective_range_basis_exists R W1 V a hai m1 e1 he1.
have [a2 ha2] := @injective_range_basis_exists R W2 V b hbi m2 e2 he2.
pose I := subspace_intersection (range_subspace a) (range_subspace b).
have [d [c [hc hd]]] := @finite_subspace_basis_exists R V n e he I.
have hi := @intersection_dimension_bound R V B hB n e he
  (range_subspace a) (range_subspace b) m1 a1 ha1 m2 a2 ha2 d c hc.
have hkd : (k <= d)%N by have := leq_trans hdim hi; rewrite leq_add2l.
pose E := @restricted_inner_product R V B I.
have hE := @restricted_inner_productP R V B hB I.
have [s hs] := @orthogonal_embedding_exists R W3 (subspace_space I)
  D E hD hE k e3 he3 d c hc hkd.
pose r := linear_comp (subspace_inclusion I) s.
have hr : is_orthogonal_map D B r by exact hs.
have hra z : range_subspace a (r z) := proj1 (subspace_valP (s z)).
have hrb z : range_subspace b (r z) := proj2 (subspace_valP (s z)).
exact: (@common_projection_factor_from_embedding R V W1 W2 W3
  B C1 C2 D hB hC1 hC2 hD f g a b hfa hgb hf hg k e3 he3 r hr hra hrb).
Qed.
