(** Federer (1969), 2.5.9, p. 100: total-function form of the absolute
    integral error in 2.5.3, p. 94. This graph compatibility lemma preserves
    the earlier partial-function definition of density. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialExtendedArithmetic
  PartialAbsolutePartsGraph PartialSimpleIntegralError SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [total_absolute_difference_graph]: compatibility needed to
    use corrected positive density in Federer 2.5.9, p. 100, erratum p. 2
    line 22 Total finite values make the subtraction defined. *)
Lemma total_absolute_difference_graph (R : realType) (X : Type) (f g : X -> R) x z :
  partial_function_graph (partial_extended_function_absolute_value
    (partial_extended_function_subtract (real_total_integrand f) (real_total_integrand g))) x z <->
  partial_function_graph (real_total_integrand (fun x => `|f x-g x|%R)) x z.
Proof.
have hf : partial_function_graph (real_total_integrand f) x (f x)%:E by apply/real_total_integrand_graph.
have hg : partial_function_graph (real_total_integrand g) x (g x)%:E by apply/real_total_integrand_graph.
have hd := @partial_subtract_finite_graph R X _ _ x (f x) (g x) hf hg.
rewrite real_total_integrand_graph; split.
- move=> [y [hy he]]; have hyv := partial_function_single_valued hy hd.
  by rewrite -he hyv abse_EFin.
- move=> he; exists (f x-g x)%R%:E; split=> //; by rewrite abse_EFin.
Qed.
