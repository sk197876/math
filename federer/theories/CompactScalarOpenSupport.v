(** Federer (1969), 4.1.7, pp. 358–359:
    scalar compact tests on U retain their
    support bound after zero extension. This
    exposes the support consequence of the
    earlier open-subspace extension law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology functions.
From Federer Require Import IsotropyGroupTopology CompactSupportFunctionUP OpenSubspaceExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_scalar_open_extension_support]:
    zero extension has support in the image
    of the original compact support, supporting
    Federer 4.1.7, pp. 358–359, through
    the earlier open-subspace compact extension.
    Only its public value laws are used. *)
Theorem compact_scalar_open_extension_support (R:realType) (X:topologicalType)
    (hHausdorff:hausdorff_space X) (U:set X) (hOpen:open U)
    (f:set_type U->R):
  @compactly_supported_continuous_functions R (set_type U) f->
  @real_function_support R X (@open_extension R X U f) `<=`
    set_val @` (@real_function_support R (set_type U) f).
Proof.
move=>hf.
pose S:=set_val @` (@real_function_support R (set_type U) f).
have hCompact:compact S.
  apply:continuous_compact hf.2;apply:continuous_subspaceT=>x.
  exact:set_type_val_continuous.
have hClosed:closed S:=compact_closed hHausdorff hCompact.
change (@real_function_support R X (@open_extension R X U f) `<=` S).
rewrite ((closure_id S).1 hClosed).
apply:closureS=>x hx.
have hU:U x.
  apply:contrapT=>hNo;apply:hx;exact:(@open_extension_out R X U f x hNo).
pose z:set_type U:=exist _ x (mem_set hU).
exists z;last by [].
apply:subset_closure=>hZero.
apply:hx;by rewrite -[x]/(set_val z) open_extensionE hZero.
Qed.
