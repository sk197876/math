(** Federer (1969), 4.1.12, pp. 368–369:
    the original interval-current series is specified by
    convergence of its finite partial sums on every
    original test. Existence is a separate theorem;
    uniqueness reuses uniqueness of real norm limits. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentEvaluation NormSequenceLimitUnique.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentWeakSequenceLimit.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).

(** Source for [is_current_weak_sequence_limit]:
    the finite partial sums have the stated current
    limit on every original test, independently of any
    chosen limit construction. This specifies the series
    of Federer 4.1.12, pp. 368–369. *)
Definition is_current_weak_sequence_limit (u:nat->C) (T:C):Prop:=
  forall phi:DT,forall epsilon:R,0<epsilon->exists k,forall L,(k<=L)%N->
    `|action (u L) phi-action T phi|<epsilon.

(** Source for [current_weak_sequence_limit_unique]:
    the original test-series specification has at most
    one current value, supporting both actual interval
    series of Federer 4.1.12, pp. 368–369.
    No additional topology on currents is introduced. *)
Theorem current_weak_sequence_limit_unique u (S T:C):
  is_current_weak_sequence_limit u S->is_current_weak_sequence_limit u T->S=T.
Proof.
move=>hS hT;apply:(@current_values_extensional R h2 n m U hU)=>phi.
exact:(@norm_sequence_limit_unique R R^o (fun t:R^o=>`|t|) (@scalar_absolute_value_norm R)
  (fun k=>action (u k) phi) (action S phi) (action T phi) (hS phi) (hT phi)).
Qed.
End CurrentWeakSequenceLimit.
