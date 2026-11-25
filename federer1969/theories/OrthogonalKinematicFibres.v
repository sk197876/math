(** Federer (1969), 3.2.48, p. 284: the exact
    original Psi fibre is the graph x to (x,g inverse x)
    over Phi inverse(A intersect g(B)). No Borel, finite-mass,
    transversality or tangent premise is used in this algebra. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  OrthogonalMaps EuclideanHomInnerCharts EuclideanRectangularAdjoint
  EuclideanOrthogonalAdjointInverse SphericalProductPreimageImage
  OrthogonalKinematicMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_kinematic_fibre_graph]: the actual
    whole-fibre equality in 3.2.48, p. 284, first
    paragraph of the proof. Both original subsets A,B
    occur unchanged. The group inverse is its actual adjoint. *)
Theorem orthogonal_kinematic_fibre_graph (R:realType) N
    (c:R_n R N) (A B:set (R_n R N)) (g:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g) ->
  [set z:Hom (R_n R N) (R_n R N)*Hom (R_n R N) (R_n R N)|
    spherical_orthogonal_preimage c A z.1 /\
    spherical_orthogonal_preimage c B z.2 /\orthogonal_kinematic_map z=g]=
  (fun x:Hom (R_n R N) (R_n R N)=>
    (x,hom_comp (euclidean_rectangular_adjoint g) x)) @`
    spherical_orthogonal_preimage c (A `&` (g @` B)).
Proof.
move=>hg; apply/seteqP; split=>z.
- move=>[hx [hy hPsi]].
  have hGY t:g (z.2 t)=z.1 t.
    have h:=congr1 (fun L:Hom (R_n R N) (R_n R N)=>L (z.2 t)) hPsi.
    change (z.1 (euclidean_rectangular_adjoint z.2 (z.2 t))=g (z.2 t)) in h.
    by rewrite (euclidean_orthogonal_adjoint_cancel hy.1) in h; exact (esym h).
  have hY:z.2=hom_comp (euclidean_rectangular_adjoint g) z.1.
    apply:hom_ext=>t; change (z.2 t=euclidean_rectangular_adjoint g (z.1 t)).
    by rewrite -hGY (euclidean_orthogonal_adjoint_cancel hg).
  exists z.1.
  + split; first exact hx.1.
    split; first exact hx.2.
    exists (z.2 c); first exact hy.2.
    exact (hGY c).
  + rewrite -hY; exact (esym (surjective_pairing z)).
- move=>[x [hx [hA [b hb hgb]]] <-].
  pose y:=hom_comp (euclidean_rectangular_adjoint g) x.
  have hy:is_orthogonal_map (@euclidean_inner_product R N)
      (@euclidean_inner_product R N) (hom_as_linear y).
    move=>a b'; change (euclidean_inner_product (euclidean_rectangular_adjoint g (x a))
      (euclidean_rectangular_adjoint g (x b'))=euclidean_inner_product a b').
    by rewrite (euclidean_orthogonal_adjoint_orthogonal hg) hx.
  have hY:y c=b.
    change (euclidean_rectangular_adjoint g (x c)=b).
    by rewrite -hgb (euclidean_orthogonal_adjoint_cancel hg).
  split; first exact (conj hx hA).
  split; first by split; last rewrite hY.
  apply:hom_ext=>t.
  have hX a:x a=g (y a).
    change (x a=g (euclidean_rectangular_adjoint g (x a))).
    exact (esym (@euclidean_orthogonal_adjoint_cancel_reverse R N g hg (x a))).
  change (x (euclidean_rectangular_adjoint y t)=g t).
  by rewrite hX (euclidean_orthogonal_adjoint_cancel_reverse hy).
Qed.
