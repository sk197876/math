(** Federer (1969), 3.4.8(10), p. 332:
    a continuous inverse section identifies
    connected components of its domain and
    image. Apply the general connected-image
    theorem and maximality of connected components. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continuous_section_component_image]:
    each ordered sheet carries the same
    components as Y_nu, supporting the
    component homeomorphisms of 3.4.8(10),
    p. 332. The actual continuous
    projection and its actual section are
    retained throughout the connected-image argument. *)
Theorem continuous_section_component_image (X Y:topologicalType)
    (P:X->Y) (V:set Y) (psi:Y->X):
  continuous P ->(forall y,V y ->{for y,continuous psi}) ->
  (forall y,V y ->P (psi y) = y) ->
  forall a,V a ->
    connected_component (psi @` V) (psi a) = psi @` connected_component V a /\
    P @` connected_component (psi @` V) (psi a) = connected_component V a.
Proof.
move=>hP hPsi hCancel a ha.
pose CY:=connected_component V a.
pose H:=psi @` V.
pose CX:=connected_component H (psi a).
have hCY:CY `<=` V:=@connected_component_sub Y V a.
have hCYAt:CY a:=connected_component_refl ha.
have hHA:H (psi a) by exists a.
have hCX:CX `<=` H:=@connected_component_sub X H (psi a).
have hCXAt:CX (psi a):=connected_component_refl hHA.
have hInverse x:H x ->psi (P x) = x.
  by move=>[y hy <-];rewrite hCancel.
have hPsiContinuous:{within CY,continuous psi}.
  apply:continuous_in_subspaceT=>y /asboolP hy;exact:hPsi y (hCY y hy).
have hConnectedImage:connected (psi @` CY):=
  connected_continuous_connected (@component_connected Y V a) hPsiContinuous.
have hImageInside:(psi @` CY) `<=` H.
  move=>x [y hy <-];exists y;first exact:hCY y hy.
  by [].
have hImageBase:(psi @` CY) (psi a) by exists a.
have hImageCX:(psi @` CY) `<=` CX:=
  @connected_component_max X H (psi @` CY) (psi a) hImageBase hImageInside hConnectedImage.
have hPConnected:connected (P @` CX):=
  connected_continuous_connected (@component_connected X H (psi a)) (continuous_subspaceT hP).
have hPInside:(P @` CX) `<=` V.
  move=>y [x hx <-];have [z hz <-]:=hCX x hx;by rewrite hCancel.
have hPBase:(P @` CX) a.
  exists (psi a);first exact:hCXAt.
  exact:hCancel a ha.
have hPCY:(P @` CX) `<=` CY:=
  @connected_component_max Y V (P @` CX) a hPBase hPInside hPConnected.
have hImage:CX = psi @` CY.
  apply/seteqP;split;last exact:hImageCX.
  move=>x hx;exists (P x).
  - apply:hPCY;by exists x.
  - exact:hInverse x (hCX x hx).
split;first exact:hImage.
apply/seteqP;split;first exact:hPCY.
move=>y hy;exists (psi y).
- change (CX (psi y));rewrite hImage;by exists y.
- exact:hCancel y (hCY y hy).
Qed.
