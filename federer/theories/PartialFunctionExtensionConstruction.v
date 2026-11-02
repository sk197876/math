(** Federer (1969), 2.3.2, p. 73: private existence construction of a total
    extension, choosing a supplied target point outside the domain.
    Downstream proofs use only the sealed abstract extension law. Source
    context and empty-target qualification: PartialFunctionExtensionUP.v. *)
From mathcomp Require Import all_boot boolp.
From Federer Require Import PartialFunctionUP PartialFunctionExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [partial_function_total_extension_exists]: existence
    argument for Federer 2.3.2, p. 73, second paragraph.
    The explicit y0 witnesses the nonempty target needed for this
    remark when the measured source may be a nonempty null space. *)
Lemma partial_function_total_extension_exists (X Y : Type)
    (f : partial_function X Y) (y0 : Y) :
  exists h : X -> Y, is_partial_function_total_extension f h.
Proof.
have hp : forall x, exists y, forall z, partial_function_graph f x z -> y = z.
  move=> x; case: (pselect (partial_function_domain f x))=> [[y hy]|hn].
  - exists y=> z hz; exact: partial_function_single_valued hy hz.
  - exists y0=> z hz; exfalso; apply: hn; by exists z.
exists (fun x => projT1 (cid (hp x)))=> x y hy.
exact: (projT2 (cid (hp x)) y hy).
Qed.
