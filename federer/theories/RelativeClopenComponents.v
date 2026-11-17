(** Federer (1969), 3.4.8(11), p. 335:
    every component of S is a component
    of T when S is open and closed
    relative to T. Thus a finite component
    count for T also bounds the count for S. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [relative_clopen_component_equation]:
    the original component identity for S
    and T, 3.4.8(11), p. 335. *)
Theorem relative_clopen_component_equation (X:topologicalType) (S T O:set X):
  open O ->S = T `&` O ->T `&` closure S `<=` S ->
  forall a,S a ->connected_component S a = connected_component T a.
Proof.
move=>hO hS hClosed a ha.
have hST:S `<=` T by move=>x hx;rewrite hS in hx;exact:hx.1.
pose C:=connected_component T a.
have hCa:C a:=connected_component_refl (hST a ha).
have hCT:C `<=` T:=@connected_component_sub X T a.
have hInside:C `<=` S.
  have hSame:C `&` S = C.
    apply:(@component_connected X T a).
    - by exists a;split.
    - exists O;first exact:hO.
      apply/seteqP;split.
      + move=>x [hCx hOther];split;first exact:hCx.
        rewrite hS in hOther;exact:hOther.2.
      + move=>x [hCx hOther];split;first exact:hCx.
        rewrite hS;split;[exact:hCT x hCx|exact:hOther].
    - exists (closure S);first exact:closed_closure.
      apply/seteqP;split.
      + move=>x [hCx hOther];split;first exact:hCx.
        exact:subset_closure hOther.
      + move=>x [hCx hOther];split;first exact:hCx.
        exact:hClosed x (conj (hCT x hCx) hOther).
  move=>x hx;have h:(C `&` S) x by rewrite hSame.
  exact:h.2.
apply/seteqP;split.
- apply:(@connected_component_max X T (connected_component S a) a
    (connected_component_refl ha) _ (@component_connected X S a)).
  move=>x hx;exact:hST x (@connected_component_sub X S a x hx).
- exact:(@connected_component_max X S C a hCa hInside (@component_connected X T a)).
Qed.

(** Source for [relative_clopen_finite_components]:
    the finite-component consequence used for the
    original nested neighbourhood, 3.4.8(11), p. 335. *)
Theorem relative_clopen_finite_components (X:topologicalType) (S T O:set X):
  open O ->S = T `&` O ->T `&` closure S `<=` S ->
  finite_set (connected_component T @` T) ->finite_set (connected_component S @` S).
Proof.
move=>hO hS hClosed hFinite.
apply:(sub_finite_set _ hFinite)=>C [a ha <-].
have hTa:T a by rewrite hS in ha;exact:ha.1.
rewrite (relative_clopen_component_equation hO hS hClosed ha).
by exists a.
Qed.
