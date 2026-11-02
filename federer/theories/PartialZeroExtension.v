(** Public zero extension for Federer (1969), 2.4.10, p. 85, derived solely
    from its sealed graph laws. Source context: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import PartialFunctionUP PartialZeroExtensionUP PartialZeroExtensionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_function_zero_extension]: public f_A
    from Federer 2.4.10, p. 85, with an explicit
    distinguished zero to support both real and extended values. *)
Definition partial_function_zero_extension (X Y : Type) (zero : Y)
    (A : set X) (f : partial_function X Y) := PartialZeroExtension.value zero A f.

(** Source for [partial_function_zero_extension_graph]: exact
    graph equation defining f_A in Federer 2.4.10, p. 85. *)
Lemma partial_function_zero_extension_graph (X Y : Type) (zero : Y)
    (A : set X) (f : partial_function X Y) x y :
  partial_function_graph (partial_function_zero_extension zero A f) x y <->
  (A x /\ partial_function_graph f x y) \/ (~ A x /\ y=zero).
Proof. exact: PartialZeroExtension.laws. Qed.

(** Source for [partial_function_zero_extension_on]: value of
    f_A on A in Federer 2.4.10, p. 85. *)
Lemma partial_function_zero_extension_on (X Y : Type) (zero : Y)
    (A : set X) (f : partial_function X Y) x y :
  A x -> (partial_function_graph (partial_function_zero_extension zero A f) x y <-> partial_function_graph f x y).
Proof.
move=> hx; rewrite partial_function_zero_extension_graph; split.
- move=> [[_ hy]|[hn _]]; first exact hy.
  by exfalso; exact: hn hx.
- by move=> hy; left; split.
Qed.

(** Source for [partial_function_zero_extension_off]: value
    zero off A in Federer 2.4.10, p. 85. *)
Lemma partial_function_zero_extension_off (X Y : Type) (zero : Y)
    (A : set X) (f : partial_function X Y) x y :
  ~ A x -> (partial_function_graph (partial_function_zero_extension zero A f) x y <-> y=zero).
Proof.
move=> hx; rewrite partial_function_zero_extension_graph; split.
- move=> [[ha _]|[_ he]]; last exact he.
  by exfalso; exact: hx ha.
- by move=> he; right; split.
Qed.

(** Source for [partial_function_zero_extension_domain]: Supporting Federer
    2.4.10, p. 85. *)
Lemma partial_function_zero_extension_domain (X Y : Type) (zero : Y)
    (A : set X) (f : partial_function X Y) :
  partial_function_domain (partial_function_zero_extension zero A f) =
    (A `&` partial_function_domain f) `|` (~` A).
Proof.
apply/seteqP; split=> x.
- move=> [y hy]; have [[ha hf]|[ha _]] := (partial_function_zero_extension_graph zero A f x y).1 hy.
  + left; split=> //; by exists y.
  + by right.
- move=> [[ha [y hy]]|ha].
  + exists y; apply/partial_function_zero_extension_graph; left; by split.
  + exists zero; apply/partial_function_zero_extension_graph; right; by split.
Qed.
