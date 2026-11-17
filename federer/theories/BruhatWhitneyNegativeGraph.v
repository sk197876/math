(** Federer (1969), 3.4.10, p. 338:
    identify the actual negative-z part of the
    cited surface with the selected analytic graph.
    The original cubic's negative-root uniqueness replaces
    any additional root-continuity or graph premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanBlockLinearMaps
  EuclideanThreeBlockCoordinates BruhatWhitneyPhysicalProjection BruhatWhitneySelectedSheet
  BruhatWhitneyAuxiliaryEquation BruhatWhitneySurfaceUP BruhatWhitneySurfaceSealed
  BruhatWhitneySurfaceAnalytic BruhatWhitneyNegativeRootUnique.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bruhat_whitney_negative_graph]: every original
    point with negative z and a prescribed prefix
    belongs to the actual implicit graph, supporting the
    regularity example in 3.4.10, p. 338. *)
Theorem bruhat_whitney_negative_graph (R:realType)
    (V:set (R_n R 2)) (psi:R_n R 2->R_n R 3):
  (forall u,V u ->@euclidean_first_block_map R 2 1 (psi u)=u /\
    @bruhat_whitney_auxiliary_equation R (psi u)=0) ->
  forall v,V (@bruhat_whitney_physical_projection R v) ->v ord_max<0 ->
  @BruhatWhitneySurface.set R v ->
  v (Ordinal (isT:(1<3)%N))=@bruhat_whitney_selected_sheet_function R psi v.
Proof.
move=>hSolutions v hv hz hS.
pose j:=Ordinal (isT:(1<3)%N).
pose Q:=@bruhat_whitney_physical_projection R.
pose w:=psi (Q v).
have [hPrefix hZero]:=hSolutions (Q v) hv.
have hFirst:=congr1 (fun u:R_n R 2=>u ord0) hPrefix.
have hLast:=congr1 (fun u:R_n R 2=>u ord_max) hPrefix.
rewrite euclidean_three_prefix_first in hFirst.
rewrite euclidean_three_prefix_second in hLast.
rewrite /Q /bruhat_whitney_physical_projection /= ffunE eqxx in hFirst.
rewrite /Q /bruhat_whitney_physical_projection /= ffunE /= in hLast.
have hActual:=@bruhat_whitney_auxiliary_projects_into_surface R w hZero.
have hRoot:((v ord0)^+2*w ord_max)*v ord_max*
    ((v ord0)^+2-v ord_max*((v ord0)^+2*w ord_max)^+2)+(v ord0)^+4=0.
  have h: @bruhat_whitney_surface_equation R
      (@bruhat_whitney_auxiliary_projection R w)=0.
    exact:(bruhat_whitney_surface_membership (@BruhatWhitneySurface.laws R) _).1 hActual.
  rewrite /bruhat_whitney_surface_equation /bruhat_whitney_auxiliary_projection !ffunE /=
    in h.
  change (w ord0=v ord0) in hFirst.
  change (w j=v ord_max) in hLast.
  by rewrite hFirst hLast in h.
have hOriginal:= (bruhat_whitney_surface_membership (@BruhatWhitneySurface.laws R) v).1 hS.
exact:(@bruhat_whitney_negative_root_unique R (v ord0) (v j)
  ((v ord0)^+2*w ord_max) (v ord_max) hz hOriginal hRoot).
Qed.
