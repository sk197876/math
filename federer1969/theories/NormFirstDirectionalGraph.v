(** Federer (1969), 4.1.2, p. 347: the single-coordinate
    derivative of a total input uses the already sealed recursive
    directional graph of 3.1.11. This is its exact first-order law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP NormedCurveDerivativeUP NormIteratedDirectionalUP
  NormIteratedDirectionalGraphUP NormIteratedDirectionalSealed PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_first_directional_graph_limit]: exact identification
    of the original two-sided first derivative D_v f in the
    commutation assertion of Federer 4.1.2, p. 347.
    No derivative existence is assumed by this graph law. *)
Theorem norm_first_directional_graph_limit (R:realType) (X Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (f:X->Y) (v a:X) (y:Y):
  partial_function_graph (@NormIteratedDirectional.value R X Y NY hNY
    (fun _=>True) f [::v]) a y <->
  punctured_norm_limit NY (fun t=>t^-1*:(f (a+t*:v)-f a)) y.
Proof.
rewrite (NormIteratedDirectional.laws hNY (fun _=>True) f [::v] a y).
split.
- move=>[g [hg [_ hLimit]]].
  have hEqual:g=f.
    apply:funext=>x; exact:(hg x (f x) (conj Logic.I (erefl (f x)))).
  by rewrite hEqual in hLimit.
- move=>hLimit; exists f; split.
  + by move=>x z [_ ->].
  + split; last exact hLimit.
    exists 1; split; first exact:ltr01.
    move=>t ht; exists (f (a+t*:v)); by split.
Qed.
