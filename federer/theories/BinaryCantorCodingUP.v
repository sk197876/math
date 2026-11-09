(** Federer (1969), 3.4.4, pp. 317–318: independent
    finite-address laws for the original binary Cantor intervals. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_binary_original_coding]: the order-preserving
    correspondence between the original level families in 3.4.4,
    p. 318, represented by finite binary addresses. The root,
    original interval endpoints, child positions, and exact level
    membership specify the coding before existence is proved.
    No replacement limit set or homeomorphism is assumed. *)
Record is_binary_original_coding (R:realType) (rho:R)
    (J:compact_real_intervals R) (H:nat->{fset compact_real_intervals R})
    (I:seq bool->compact_real_intervals R) (a:seq bool->R):Prop:={
  (** Source for [binary_original_coding_root]: the original
      unit root in 2.10.28, p. 193, used in 3.4.4,
      p. 318. The empty address has lower endpoint zero. *)
  binary_original_coding_root:I [::]=J /\a [::]=0;
  (** Source for [binary_original_coding_intervals]: the original
      level-j intervals have length rho^j, 3.4.4, p. 318. *)
  binary_original_coding_intervals:forall w,
    val (I w)=(`[a w,a w+rho^+(size w)]:set (real_line_metric R));
  (** Source for [binary_original_coding_extension]: left and
      right original children occupy the two endpoint positions,
      3.4.4, p. 318, by 2.10.28, p. 193. *)
  binary_original_coding_extension:forall w b,
    a (rcons w b)=a w+(if b then 1-rho else 0)*rho^+(size w);
  (** Source for [binary_original_coding_levels]: every original
      interval, and only an original interval, occurs at its
      address length, 3.4.4, p. 318. Injectivity and
      the induced correspondence are subsequent conclusions. *)
  binary_original_coding_levels:forall j S,
    S \in H j <->exists w,size w=j /\I w=S
}.
