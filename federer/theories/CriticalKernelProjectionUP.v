(** Federer (1969), 3.4.3, p. 317: laws of the
    orthogonal kernel coordinates selected before the joint chart. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  OrthogonalMaps AdjointUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_critical_kernel_projection]: q belongs to
    O*(m,m-nu) and im q*=ker Df(a), 3.4.3, p. 317.
    Here alpha is L Df(a), whose kernel is proved to be the
    same. The actual adjoint and its image are specified
    before the finite-frame existence proof. *)
Record is_critical_kernel_projection (R:realType) nu l
    (alpha:Hom (R_n R (nu+l)) (R_n R nu))
    (q:{linear R_n R (nu+l)->R_n R l})
    (j:{linear R_n R l->R_n R (nu+l)}):Prop:={
  (** Source for [critical_kernel_projection_orthogonal]: q*
      is an orthogonal injection, 3.4.3, p. 317. *)
  critical_kernel_projection_orthogonal:is_orthogonal_map
    (@euclidean_inner_product R l) (@euclidean_inner_product R (nu+l)) j;
  (** Source for [critical_kernel_projection_adjoint]: q is the
      actual adjoint of that injection, 3.4.3, p. 317. *)
  critical_kernel_projection_adjoint:is_adjoint
    (@euclidean_inner_product R l) (@euclidean_inner_product R (nu+l)) j q;
  (** Source for [critical_kernel_projection_image]: the image
      of q* is exactly the original kernel, 3.4.3, p. 317. *)
  critical_kernel_projection_image:forall x,alpha x=0 <->exists u,j u=x
}.
