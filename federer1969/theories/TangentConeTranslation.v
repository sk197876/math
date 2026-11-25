(** Federer (1969), 3.4.11, p. 338:
    translating the original centre a to zero leaves
    the actual tangent vectors unchanged. This connection
    uses the original two strict approximation inequalities;
    it assumes no differentiability or analytic structure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_tangent_source_translation]: the initial
    reduction to a=0 in 3.4.11, p. 338.
    The original tangent cone is preserved exactly under
    the actual source translation, in every source dimension. *)
Theorem norm_tangent_source_translation (R:realType) (X:lmodType R)
    (N:X->R) (S:set X) (a:X):
  norm_tangent_cone N [set x|S (a+x)] 0=norm_tangent_cone N S a.
Proof.
apply:funext=>v;apply:propext;split=>hTangent e he.
- have [x [r [hx [hr [hSmall hNear]]]]]:=hTangent e he.
  exists (a+x),r;split;first exact:hx.
  split;first exact:hr.
  rewrite addrAC subrr add0r.
  by rewrite subr0 in hSmall hNear;split.
- have [x [r [hx [hr [hSmall hNear]]]]]:=hTangent e he.
  exists (x-a),r;split;first by change (S (a+(x-a)));rewrite addrC subrK.
  split;first exact:hr.
  rewrite subr0;by split.
Qed.
