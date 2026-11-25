(** Federer (1969), 3.4.5, p. 321: the
    Boolean closure of analytic varieties consists of finite
    unions of differences of original varieties. The supporting
    normal-form argument is stated for arbitrary set families. *)
From mathcomp Require Import all_boot boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_difference_union]: the actual
    finite union of pairs S_i minus T_i printed in
    3.4.5, p. 321. The finite fold selects
    no representatives or auxiliary geometric objects. *)
Fixpoint finite_difference_union (X:Type) (F:seq (set X*set X)):set X:=
  match F with [::]=>set0|p::K=>(p.1 `\` p.2) `|` finite_difference_union K end.

(** Source for [has_finite_difference_form]: the exact
    finite-union-of-differences form in 3.4.5, p. 321,
    with both members of each pair in the original class. *)
Definition has_finite_difference_form (X:choiceType) (C:set (set X)) (S:set X):=
  exists F:seq (set X*set X),(forall p,p \in F ->C p.1 /\C p.2) /\S=finite_difference_union F.

(** Source for [finite_boolean_set_closure]: the sets
    obtained from the original family using finitely many
    unions, intersections and differences, 3.4.5, p. 321. *)
Inductive finite_boolean_set_closure (X:choiceType) (C:set (set X)):set (set X):=
| finite_boolean_base S:C S ->finite_boolean_set_closure C S
| finite_boolean_union S T:finite_boolean_set_closure C S ->finite_boolean_set_closure C T ->
    finite_boolean_set_closure C (S `|` T)
| finite_boolean_intersection S T:finite_boolean_set_closure C S ->finite_boolean_set_closure C T ->
    finite_boolean_set_closure C (S `&` T)
| finite_boolean_difference S T:finite_boolean_set_closure C S ->finite_boolean_set_closure C T ->
    finite_boolean_set_closure C (S `\` T).
