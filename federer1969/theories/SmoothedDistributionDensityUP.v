(** Federer (1969), 4.1.2, p. 347: the
    displayed dual-valued density is specified by its
    exact pairings with all y, independently of
    its existence and smoothness proofs. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_smoothed_distribution_density]: the defining
    equation (y,g_epsilon(z))=T_x[Phi_epsilon(x-z)y]
    in Federer 4.1.2, p. 347. B is
    the actual translated kernel test family. *)
Definition is_smoothed_distribution_density (R:realType) (X:Type) (Y DT YD:lmodType R)
    (B:X->Hom Y DT) (T:Hom DT R^o) (ed:Hom YD (Hom Y R^o)) (g:X->YD):Prop:=
  forall z y,ed (g z) y=T (B z y).
