(** Federer (1969), 4.1.11, p. 365: the original
    oriented-simplex family is opaque. Its public interface
    exposes exactly the independently specified point base
    and original point-join recursion. Existence is proved
    separately; the construction is hidden. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations CurrentSpaces CurrentDensityUP OrientedSimplexCurrentUP
  OrientedSimplexCurrentExistence OrientedSimplexCurrentFamilyLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type OrientedSimplexCurrentSignature.
(** Source for [value]: the original ordered m-simplex
    [u_0,...,u_m] in R^n, Federer 4.1.11, p. 365.
    Neither nondegeneracy nor m<=n is imposed. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (n m:nat),
  ('I_(m.+1)->R_n R n)->@full_current_space R h2 n m.
(** Source for [laws]: [u]=delta_u and the original
    successive point-join recursion, Federer 4.1.11,
    p. 365. No boundary, mass or alternation law is assumed. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n:nat),
  @is_oriented_simplex_current_family R h2 n (@value R h2 n).
End OrientedSimplexCurrentSignature.
Module OrientedSimplexCurrent:OrientedSimplexCurrentSignature.
(** Source for [family]: a private witness of the
    original independent family laws, supporting Federer
    4.1.11, p. 365. The module signature hides this
    implementation helper. *)
Definition family (R:realType) (h2:(1+1:R)!=0) n:
    forall m:nat,('I_(m.+1)->R_n R n)->@full_current_space R h2 n m:=
  projT1 (cid (@oriented_simplex_current_family_exists R h2 n)).
(** Source for [value]: seal the proved original
    oriented-simplex witness, Federer 4.1.11, p. 365. *)
Definition value (R:realType) (h2:(1+1:R)!=0) n m
    (v:'I_(m.+1)->R_n R n):@full_current_space R h2 n m:=@family R h2 n m v.
(** Source for [laws]: the opaque family satisfies its
    independently specified original point and join laws,
    supporting Federer 4.1.11, p. 365. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) n:
  @is_oriented_simplex_current_family R h2 n (@value R h2 n).
Proof. exact:(projT2 (cid (@oriented_simplex_current_family_exists R h2 n))). Qed.
End OrientedSimplexCurrent.
