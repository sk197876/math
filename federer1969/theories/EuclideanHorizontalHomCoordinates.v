(** Federer (1969), 3.2.28(2), printed p. 264:
    Z(g) is isomorphic to Hom(R^m,R^(n-m)). These
    exact linear coordinate laws use only the abstract
    orthogonal-complement specification. No global coordinates
    or basis are chosen. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorUP Bilinear ModuleQuotient SubspaceCarrier
  GrassmannAbbreviations EuclideanRectangularAdjoint
  EuclideanFrameComplementUP EuclideanStiefelSubspaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_frame_complement_hom_normal]: maps
    with values in the normal coordinates belong to Z(g),
    supporting its dimension in Federer 3.2.28(2), p. 264. *)
Lemma euclidean_frame_complement_hom_normal (R:realType) m n k
    (g:Hom (R_n R m) (R_n R n))
    (a:Hom (R_n R k) (R_n R n)) (p:Hom (R_n R n) (R_n R k))
    (hC:is_euclidean_frame_complement g a p) (u:Hom (R_n R m) (R_n R k)):
  euclidean_stiefel_horizontal_subspace g (hom_comp a u).
Proof.
apply:hom_ext=>x.
change (euclidean_rectangular_adjoint g (a (u x))=0).
exact:(@frame_complement_normal R m n k g a p hC (u x)).
Qed.

(** Source for [euclidean_horizontal_hom_coordinates_exist]:
    the horizontal subspace has exact Hom coordinates,
    supporting dim Z(g)=m(n-m) in Federer 3.2.28(2),
    p. 264. Both linear inverses and their actual
    composition formulas are proved from normal-range laws. *)
Theorem euclidean_horizontal_hom_coordinates_exist (R:realType) m n k
    (g:Hom (R_n R m) (R_n R n))
    (a:Hom (R_n R k) (R_n R n)) (p:Hom (R_n R n) (R_n R k))
    (hC:is_euclidean_frame_complement g a p):
  exists
    (f:Hom (Hom (R_n R m) (R_n R k))
      (subspace_space (euclidean_stiefel_horizontal_subspace g)))
    (q:Hom (subspace_space (euclidean_stiefel_horizontal_subspace g))
      (Hom (R_n R m) (R_n R k))),
    cancel f q /\ cancel q f /\
    (forall u,subspace_val (f u)=hom_comp a u) /\
    forall h,q h=hom_comp p (subspace_val h).
Proof.
pose Z:=subspace_space (euclidean_stiefel_horizontal_subspace g).
pose U:=Hom (R_n R m) (R_n R k).
pose F (u:U):Z:=subspace_lift (euclidean_frame_complement_hom_normal hC u).
have hF:linear F.
  move=>c u v; apply:subspace_val_injective.
  rewrite linearD linearZ /F !subspace_liftE.
  apply:hom_ext=>x.
  rewrite !hom_compE !hom_addE !hom_scaleE linearD linearZ.
  reflexivity.
pose f:=@HomMap R U Z F (introT (asboolP _) hF).
pose Q (h:Z):U:=hom_comp p (subspace_val h).
have hQ:linear Q.
  move=>c h z; rewrite /Q linearD linearZ.
  apply:hom_ext=>x.
  rewrite !hom_compE !hom_addE !hom_scaleE linearD linearZ.
  reflexivity.
pose q:=@HomMap R Z U Q (introT (asboolP _) hQ).
exists f,q; split.
- move=>u; apply:hom_ext=>x.
  change (p (a (u x))=u x).
  exact:(@frame_complement_cancel R m n k g a p hC (u x)).
split.
- move=>h; apply:subspace_val_injective.
  change (hom_comp a (hom_comp p (subspace_val h))=subspace_val h).
  apply:hom_ext=>x; rewrite !hom_compE.
  apply:(@frame_complement_range R m n k g a p hC (subspace_val h x)).
  have hz:=subspace_valP h.
  change (hom_comp (euclidean_rectangular_adjoint g) (subspace_val h)=0) in hz.
  exact:(congr1 (fun L:Hom (R_n R m) (R_n R m)=>L x) hz).
split; first by move=>u.
by move=>h.
Qed.
