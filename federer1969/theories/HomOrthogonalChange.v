(** Federer (1969), 1.7.9, p. 35, penultimate paragraph: orthogonal changes
    of source and target coordinates act by the tensor of the source dual
    and target maps and preserve the norm of linear maps. The target may
    have arbitrary dimension. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerDual HomInner
  Hom Gamma GammaNaturality LinearBasis OrthogonalMaps
  TensorUP TensorProduct TensorMaps TensorInner TensorInnerNaturality
  TensorMapIsomorphism OneCovectorOrthogonal AlternatingDual AlternatingCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Changes.
Variable R : rcfType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variables (s : {linear V -> V}) (t : {linear W -> W}).
Hypothesis hs : is_orthogonal_map B B s.
Hypothesis ht : is_orthogonal_map C C t.
Local Notation ds := (GRing.Linear.clone _ _ _ _ (@A_m_dual R V V R^o s 1) _).

(** Source for [orthogonal_change_tensor_automorphism]: Federer
    1.7.9, p. 35, the tensor of the source dual and target
    orthogonal automorphisms is an orthogonal automorphism. *)
Theorem orthogonal_change_tensor_automorphism : bijective t ->
  is_orthogonal_map (tensor_inner (inner_dual_productP hB he) hC)
    (tensor_inner (inner_dual_productP hB he) hC) (tensor_map ds t) /\
  bijective (tensor_map ds t).
Proof.
move=> htbij; split.
- exact: tensor_map_orthogonal (one_covector_orthogonal hB he hs) ht.
- apply: tensor_map_bijective; last exact htbij.
  exact (@one_covector_orthogonal_bijective R V B hB n e he s hs).
Qed.

(** Source for [orthogonal_change_Gamma]: Federer 1.7.9,
    p. 35, the tensor map carries Gamma(f) to Gamma(t composed
    with f composed with s). This is the previously proved
    naturality identity specialised to orthogonal coordinates. *)
Theorem orthogonal_change_Gamma (f : Hom V W) :
  tensor_map ds t (@Gamma R V W (Finite.clone 'I_n _) e he f) =
  @Gamma R V W (Finite.clone 'I_n _) e he (Hom_sandwich s t f).
Proof.
exact: esym (@Gamma_natural R V W V W s t
  (Finite.clone 'I_n _) (Finite.clone 'I_n _) e e he he f).
Qed.

(** Source for [hom_inner_orthogonal_change]: Federer 1.7.9,
    p. 35, supporting product invariance under orthogonal changes
    of coordinates. Target surjectivity is unnecessary for this
    stronger isometry statement. *)
Theorem hom_inner_orthogonal_change (f g : Hom V W) :
  hom_inner hB hC he (Hom_sandwich s t f) (Hom_sandwich s t g) =
  hom_inner hB hC he f g.
Proof.
rewrite !hom_innerE -!orthogonal_change_Gamma.
exact (@tensor_map_orthogonal R (A_m V R^o 1) W (A_m V R^o 1) W
  _ _ _ _ (inner_dual_productP hB he) hC (inner_dual_productP hB he) hC
  ds t (@one_covector_orthogonal R V B hB n e he s hs) ht
  (@Gamma R V W (Finite.clone 'I_n _) e he f)
  (@Gamma R V W (Finite.clone 'I_n _) e he g)).
Qed.

(** Source for [hom_norm_orthogonal_change]: Federer 1.7.9,
    p. 35, the printed equality of the norm of f and of
    t composed with f composed with s. *)
Theorem hom_norm_orthogonal_change (f : Hom V W) :
  hom_norm hB hC he (Hom_sandwich s t f) = hom_norm hB hC he f.
Proof.
apply: inner_norm_value; first exact: inner_norm_nonnegative.
by rewrite inner_norm_sqr hom_inner_orthogonal_change.
Qed.
End Changes.
