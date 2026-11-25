(** Federer (1969), 4.1.5, p. 350: the
    continuous compact scalar cutoff h removes a small
    norm tail of w. These pointwise and support laws
    specify that cutoff before proving existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_compact_norm_tail_cutoff]: the h
    with h||w||=(||w||-eta g)+ in Federer 4.1.5,
    p. 350, where g equals one on a neighbourhood
    of the support of w. On that support this is
    the positive tail (||w||-eta)+. *)
Record is_compact_norm_tail_cutoff (R:realType) (X:topologicalType)
    (Y:lmodType R) (NY:Y->R) (w:X->Y) (eta:R) (h:X->R):Prop:={
  (** Source for [compact_norm_tail_function]: h belongs
      to K(U), Federer 4.1.5, p. 350. *)
  compact_norm_tail_function:compactly_supported_continuous_functions h;
  (** Source for [compact_norm_tail_range]: h is positive
      and at most one, for the norm decomposition in
      Federer 4.1.5, p. 350. *)
  compact_norm_tail_range:forall x,0<=h x<= 1;
  (** Source for [compact_norm_tail_product]: the original
      positive-part identity in Federer 4.1.5, p. 350,
      on the support where g equals one. *)
  compact_norm_tail_product:forall x,h x*NY (w x)=Num.max (NY (w x)-eta) 0;
  (** Source for [compact_norm_tail_small_zero]: h vanishes
      on the small-norm region, supporting both original
      convolution inequalities of Federer 4.1.5, p. 350. *)
  compact_norm_tail_small_zero:forall x,NY (w x)<eta ->h x=0;
  (** Source for [compact_norm_tail_support]: the tail
      cutoff stays inside the original norm support of
      w, Federer 4.1.5, p. 350. *)
  compact_norm_tail_support:real_function_support h `<=` real_function_support (fun x=>NY (w x))
}.
