(** Federer (1969), 2.4.10, p. 85: supporting set and graph identities for
    the zero extension used to define integrals over subsets. Source
    editions: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
From Federer Require Import PartialFunctionUP PartialFunctionPostcomposition PartialZeroExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_zero_extension_preimage]: supporting
    inverse-image formula for measurability of f_A in
    Federer 2.4.10, p. 85; zero may or may
    not belong to the target set. *)
Lemma partial_zero_extension_preimage (X Y : Type) (zero : Y)
    (A : set X) (f : partial_function X Y) (U : set Y) :
  partial_function_preimage (partial_function_zero_extension zero A f) U =
    (A `&` partial_function_preimage f U) `|` [set x | ~ A x /\ U zero].
Proof.
apply/seteqP; split=> x.
- move=> [y [hy hU]]; have [[ha hf]|[ha he]] := (partial_function_zero_extension_graph zero A f x y).1 hy.
  + left; split=> //; exists y; by split.
  + right; split=> //; by rewrite -he.
- move=> [[ha [y [hy hU]]]|[ha hU]].
  + exists y; split=> //; apply/partial_function_zero_extension_graph; left; by split.
  + exists zero; split=> //; apply/partial_function_zero_extension_graph; right; by split.
Qed.

(** Source for [partial_zero_extension_postcompose]: supporting commutation
    of f_A with an operation sending zero to zero, used for parts and
    absolute values in Federer 2.4.10, p. 85 *)
Lemma partial_zero_extension_postcompose (X Y Z : Type) (zero : Y) (zero' : Z)
    (A : set X) (f : partial_function X Y) (p : Y -> Z) x z :
  p zero=zero' ->
  (partial_function_graph (partial_function_postcompose (partial_function_zero_extension zero A f) p) x z <->
   partial_function_graph (partial_function_zero_extension zero' A (partial_function_postcompose f p)) x z).
Proof.
move=> hp; rewrite partial_function_zero_extension_graph; split.
- move=> [y [hy hyz]]; have [[ha hf]|[ha he]] := (partial_function_zero_extension_graph zero A f x y).1 hy.
  + left; split=> //; exists y; by split.
  + right; split=> //; by rewrite -hyz he hp.
- move=> [[ha [y [hy hyz]]]|[ha he]].
  + exists y; split=> //; apply/partial_function_zero_extension_graph; left; by split.
  + exists zero; split; last by rewrite hp he.
    apply/partial_function_zero_extension_graph; right; by split.
Qed.

(** Source for [partial_zero_extension_empty_graph]: the empty
    subset integral of Federer 2.4.10, p. 85,
    uses a total zero function, even when f has empty domain. *)
Lemma partial_zero_extension_empty_graph (X Y : Type) (zero : Y)
    (f : partial_function X Y) x y :
  partial_function_graph (partial_function_zero_extension zero set0 f) x y <-> y=zero.
Proof. apply: partial_function_zero_extension_off; by []. Qed.

(** Source for [partial_zero_extension_whole_graph]: the whole
    subset integral of Federer 2.4.10, p. 85,
    retains the original graph and domain. *)
Lemma partial_zero_extension_whole_graph (X Y : Type) (zero : Y)
    (f : partial_function X Y) x y :
  partial_function_graph (partial_function_zero_extension zero setT f) x y <-> partial_function_graph f x y.
Proof. exact: partial_function_zero_extension_on I. Qed.

(** Source for [partial_zero_extension_intersection_graph]:
    successive restrictions in the subset integrals of Federer
    2.4.10, p. 85, are restriction to the intersection. *)
Lemma partial_zero_extension_intersection_graph (X Y : Type) (zero : Y)
    (A B : set X) (f : partial_function X Y) x y :
  partial_function_graph (partial_function_zero_extension zero A
    (partial_function_zero_extension zero B f)) x y <->
  partial_function_graph (partial_function_zero_extension zero (A `&` B) f) x y.
Proof.
rewrite (partial_function_zero_extension_graph zero A _)
  (partial_function_zero_extension_graph zero (A `&` B) f); split.
- move=> [[ha hy]|[ha he]].
  + have [[hb hf]|[hb he]] := (partial_function_zero_extension_graph zero B f x y).1 hy.
    * left; by split; [split|].
    * right; split=> //; by move=> [_ hbx]; exact: hb hbx.
  + right; split=> //; by move=> [hax _]; exact: ha hax.
- move=> [[[ha hb] hf]|[hn he]].
  + left; split=> //; apply/partial_function_zero_extension_graph; left; by split.
  + have [ha|ha] := pselect (A x).
    * left; split=> //; apply/partial_function_zero_extension_graph; right; split=> // hb.
      apply: hn; by split.
    * right; by split.
Qed.
