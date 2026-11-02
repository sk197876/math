(** Federer (1969), 2.5.20, p. 114: supporting approximation for the final
    variation-measure identification. If |v|<=a and e>0, then r=v/(a+e) lies
    in the unit interval in absolute value and a*r approximates v within e.
    This is an expanded elementary step, not a separately numbered assertion
    of Federer. Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [regularized_scalar_ratio_bound]: the bounded
    test v/(a+e), supporting the final equality of variation
    measures in Federer 2.5.20, p. 114. *)
Lemma regularized_scalar_ratio_bound (R : realType) (a v e : R) :
  0<=a -> `|v|<=a -> 0<e -> `|v/(a+e)|<=1.
Proof.
move=> ha hv he; have hden : 0<a+e by lra.
rewrite normf_div (ger0_norm (ltW hden)) ler_pdivrMr // mul1r.
lra.
Qed.

(** Source for [regularized_scalar_ratio_error]: uniform
    error bound for a*v/(a+e), supporting the approximation
    of variation tests in Federer 2.5.20, p. 114. *)
Lemma regularized_scalar_ratio_error (R : realType) (a v e : R) :
  0<=a -> `|v|<=a -> 0<e -> `|a*(v/(a+e))-v|<=e.
Proof.
move=> ha hv he; have hden : 0<a+e by lra.
have hratio := regularized_scalar_ratio_bound ha hv he.
have hve : v=(a+e)*(v/(a+e)) by rewrite mulrC divfK ?gt_eqF.
have hid : a*(v/(a+e))-v= -e*(v/(a+e)).
  rewrite {2}hve -mulrBl.
  by rewrite opprD addrA subrr add0r.
rewrite hid normrM normrN (ger0_norm (ltW he)).
have h := ler_wpM2l (ltW he) hratio; by rewrite mulr1 in h.
Qed.
