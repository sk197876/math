(** Federer (1969), 3.2.48, p. 285: the printed
    differential of Psi on the actual orthogonal tangents.
    The ambient adjoint polynomial differential is converted to
    the original inverse formula using the actual Gram equation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm OrthogonalMaps EuclideanHomInnerCharts EuclideanRectangularAdjoint
  EuclideanOrthogonalAdjointInverse EuclideanGramDifferentialAlgebra
  SphericalOrthogonalTangents TangentConeUP OrthogonalKinematicMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_tangent_adjoint]: the derivative
    of inversion used in 3.2.48, p. 285,
    obtained on actual orthogonal tangents from 3.2.28(1),
    p. 263. It is v adjoint = -y inverse v y inverse. *)
Lemma orthogonal_tangent_adjoint (R:realType) N
    (y v:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear y) ->
  norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R N N))
    [set g|is_orthogonal_map (@euclidean_inner_product R N)
      (@euclidean_inner_product R N) (hom_as_linear g)] y v ->
  euclidean_rectangular_adjoint v=
    -hom_comp (euclidean_rectangular_adjoint y) (hom_comp v (euclidean_rectangular_adjoint y)).
Proof.
move=>hy hv.
rewrite (spherical_orthogonal_tangent_gram hy) in hv.
apply:hom_ext=>z.
have hValue:=congr1 (fun L:Hom (R_n R N) (R_n R N)=>L (euclidean_rectangular_adjoint y z)) hv.
rewrite euclidean_gram_differentialE in hValue.
change (euclidean_rectangular_adjoint v (y (euclidean_rectangular_adjoint y z))+
  euclidean_rectangular_adjoint y (v (euclidean_rectangular_adjoint y z))=0) in hValue.
rewrite (euclidean_orthogonal_adjoint_cancel_reverse hy) in hValue.
change (euclidean_rectangular_adjoint v z=
  -euclidean_rectangular_adjoint y (v (euclidean_rectangular_adjoint y z))).
by apply/eqP; rewrite -addr_eq0; apply/eqP.
Qed.

(** Source for [orthogonal_kinematic_tangent_formula]: the first
    displayed D Psi formula and its conjugated subtraction
    in 3.2.48, p. 285. No differentiability or
    derivative-field premise is added to the numbered geometry;
    this algebra applies to the ambient derivative already proved. *)
Theorem orthogonal_kinematic_tangent_formula (R:realType) N
    (x y u v:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear x) ->
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear y) ->
  norm_tangent_cone (inner_norm (@euclidean_hom_inner_productP R N N))
    [set g|is_orthogonal_map (@euclidean_inner_product R N)
      (@euclidean_inner_product R N) (hom_as_linear g)] y v ->
  hom_comp u (euclidean_rectangular_adjoint y)+hom_comp x (euclidean_rectangular_adjoint v)=
    hom_comp x (hom_comp
      (hom_comp (euclidean_rectangular_adjoint x) u-
        hom_comp (euclidean_rectangular_adjoint y) v)
      (euclidean_rectangular_adjoint y)).
Proof.
move=>hx hy hv.
rewrite (@orthogonal_tangent_adjoint R N y v hy hv).
apply:hom_ext=>z.
change (u (euclidean_rectangular_adjoint y z)+
    x (-euclidean_rectangular_adjoint y (v (euclidean_rectangular_adjoint y z)))=
  x (euclidean_rectangular_adjoint x (u (euclidean_rectangular_adjoint y z))-
    euclidean_rectangular_adjoint y (v (euclidean_rectangular_adjoint y z)))).
have hNegative:x (-euclidean_rectangular_adjoint y (v (euclidean_rectangular_adjoint y z)))=
    -x (euclidean_rectangular_adjoint y (v (euclidean_rectangular_adjoint y z))).
  by rewrite linearN.
have hDifference:=linB (hom_linear x)
  (euclidean_rectangular_adjoint x (u (euclidean_rectangular_adjoint y z)))
  (euclidean_rectangular_adjoint y (v (euclidean_rectangular_adjoint y z))).
rewrite hNegative hDifference.
have hCancel:=@euclidean_orthogonal_adjoint_cancel_reverse R N x hx
  (u (euclidean_rectangular_adjoint y z)).
exact (congr2 (fun a b:R_n R N=>a-b) (esym hCancel) erefl).
Qed.
