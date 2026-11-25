(** Federer (1969), 3.3.4, p. 292:
    both antipodal projective directions lie
    in the same original linear kernel.
    Positive normalization is undone by
    its actual finite norm. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import InnerProductUP InnerNorm InnerUnitNormalization
  SymmetricSquareGeometry StructureProjectiveDirections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [structure_direction_fibre_kernel]:
    supporting F inverse R contained in
    D in Federer 3.3.4, p. 292.
    If the actual unit direction v is
    killed by a linear map, every
    nonzero original vector whose normalized
    projective square equals T(v) is
    killed too. Both signs are retained. *)
Theorem structure_direction_fibre_kernel (R:realType) (V W:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (L:{linear V->W}) (u v:V):
  0<inner_norm hB u ->inner_norm hB v= 1 ->L v=0 ->
  inner_projective_square (inner_unit_normalization hB u)=inner_projective_square v ->L u=0.
Proof.
move=>hu hv hKernel hSquare.
have hRecover:u=inner_norm hB u*:inner_unit_normalization hB u.
  by rewrite /inner_unit_normalization scalerA mulfV ?gt_eqF // scale1r.
have hDirection:inner_unit_normalization hB u=v \/inner_unit_normalization hB u= -v.
  exact:(structure_projective_direction_fibre hu hv).1 hSquare.
have hUnitKernel:L (inner_unit_normalization hB u)=0.
  case:hDirection=>hDirection; rewrite hDirection.
  - exact:hKernel.
  - by rewrite linearN hKernel oppr0.
have hMapRecover:=congr1 L hRecover.
rewrite linearZZ hUnitKernel scaler0 in hMapRecover.
exact:hMapRecover.
Qed.
