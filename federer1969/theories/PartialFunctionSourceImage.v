(** Federer (1969), 2.3.1, p. 72: functions as
    single-valued graphs. This supporting relabelling along
    an injective source map is used for the original
    scalar time parameter in 4.1.9, pp. 363–364.
    No value is assigned outside the original image domain. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import PartialFunctionUP PartialFunctionPrecomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section PartialFunctionSourceImage.
Variables X Y Z:Type.
Variable u:X->Y.
Hypothesis hu:injective u.
Variable f:partial_function X Z.

(** Source for [partial_function_source_image]: the exact
    original graph with source labels changed by an
    injection, supporting the scalar-coordinate integrals
    in Federer 4.1.9, pp. 363–364, through the
    graph convention of 2.3.1, p. 72. *)
Definition partial_function_source_image:partial_function Y Z.
Proof.
refine (@Build_partial_function Y Z
  (fun y z=>exists x,u x=y /\partial_function_graph f x z) _).
move=>y a b [x [hX hA]] [v [hV hB]].
have hSame:x=v:=hu (eq_trans hX (esym hV)).
subst v;exact:partial_function_single_valued hA hB.
Defined.

(** Source for [partial_function_source_image_cancel]:
    returning to the original source preserves exactly
    the original partial graph, supporting Federer
    4.1.9, pp. 363–364, through 2.3.1, p. 72. *)
Lemma partial_function_source_image_cancel x z:
  partial_function_graph (partial_function_precompose u partial_function_source_image) x z <->
    partial_function_graph f x z.
Proof.
split.
- move=>[v [hV hF]];have hSame:v=x:=hu hV;by subst v.
- move=>hF;exists x;by split.
Qed.
End PartialFunctionSourceImage.
