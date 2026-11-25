(** Federer (1969), 4.1.1, p. 344: independent
    laws for an auxiliary locally finite selection used
    to prove common compact support. Existence of such
    data is proved only under failure of a common
    compact support; it is never assumed for a bounded
    family of evaluations. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom NormLocallyFiniteFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_smooth_dual_hump]: a locally finite
    smooth sequence with unbounded selected evaluations,
    supporting the contradiction in Federer 4.1.1,
    p. 344. These are properties of supplied
    data; no existence or convergence is implicit. *)
Record is_smooth_dual_hump (R:realType) (X Y E:lmodType R)
    (NX:X->R) (U:X->Prop) (ev:E->X->Y) (T:nat->Hom E R^o)
    (f:nat->E) (k:nat->nat):Prop:={
  (** Source for [smooth_dual_hump_local_finiteness]: the
      selected increments have a locally finite smooth
      sum, supporting Federer 4.1.1, p. 344. *)
  smooth_dual_hump_local_finiteness:is_norm_locally_finite_function_family NX U (@setT nat) (fun j x=>ev (f j) x);
  (** Source for [smooth_dual_hump_prescribed_partial]: the
      nth selected evaluation of the next partial sum
      is n+1, supporting Federer 4.1.1,
      p. 344. *)
  smooth_dual_hump_prescribed_partial:forall n,T (k n) (\sum_(j<n.+1) f j)=n.+1%:R;
  (** Source for [smooth_dual_hump_tail_zero]: later
      increments have zero earlier selected evaluation,
      supporting Federer 4.1.1, p. 344. *)
  smooth_dual_hump_tail_zero:forall n m,(n<m)%N ->T (k n) (f m)=0
}.
