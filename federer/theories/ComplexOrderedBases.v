(** Federer (1969), 1.6.6, pp. 26-27: the real and mixed one-form bases,
    ordered in two blocks. Reindexing retains the basis assertions while
    putting all unbarred indices before barred ones. Source context are
    recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates ScalarRestriction ComplexScalarSealed
  ComplexCoefficientAlgebra ComplexValuedForms ComplexRealBasis ComplexOneFormBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Ordered.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation ii := (ComplexScalars.ii R).
Variable V : lmodType C.
Local Notation VR := (restricted_space embed V).
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation I := (Finite.clone ('I_n * bool)%type _).
Local Notation J := (Finite.clone ('I_n + 'I_n)%type _).

(** Source for [complex_pair_sum]: Federer 1.6.6, pp. 26-27,
    displayed bases. Supporting conversion from paired to block indices. *)
Definition complex_pair_sum (j : I) : J := if j.2 then inr j.1 else inl j.1.
(** Source for [complex_sum_pair]: Federer 1.6.6, pp. 26-27,
    displayed bases. Inverse conversion of the indices. *)
Definition complex_sum_pair (j : J) : I :=
  match j with inl i => (i,false) | inr i => (i,true) end.
(** Source for [complex_pair_sumK]: Federer 1.6.6, pp. 26-27,
    displayed bases. Supporting cancellation of the index conversion. *)
Lemma complex_pair_sumK : cancel complex_pair_sum complex_sum_pair.
Proof. by move=> [j []]. Qed.
(** Source for [complex_sum_pairK]: Federer 1.6.6, pp. 26-27,
    displayed bases. Supporting reverse cancellation. *)
Lemma complex_sum_pairK : cancel complex_sum_pair complex_pair_sum.
Proof. by move=> [j|j]. Qed.

(** Source for [ordered_real_basis]: Federer 1.6.6, p. 26,
    real basis e_j,i e_j. Here the same basis is ordered in two blocks. *)
Definition ordered_real_basis (j : 'I_(n+n)) : VR :=
  match split j with inl i => e i | inr i => ii *: e i end.

(** Source for [ordered_real_basisP]: Federer 1.6.6, p. 26,
    real basis. Reordering the paired basis preserves both independence
    and spanning, also when n=0. *)
Theorem ordered_real_basisP : is_basis ordered_real_basis.
Proof.
have hs := @basis_reindex R (Choice.clone I _) (Choice.clone J _) VR
  (realified_basis e) (realified_basisP he) complex_pair_sum complex_sum_pair
  complex_pair_sumK complex_sum_pairK.
have ho := @basis_reindex R (Choice.clone J _) (Choice.clone 'I_(n+n) _) VR
  (fun j => realified_basis e (complex_sum_pair j)) hs
  (@unsplit n n) (@split n n) (@unsplitK n n) (@splitK n n).
apply: basis_congr ho => j.
by rewrite /ordered_real_basis /complex_sum_pair /realified_basis; case: (split j).
Qed.

(** Source for [ordered_mixed_one_form]: Federer 1.6.6, p. 27,
    mixed basis. The first block consists of alpha_j, the second
    of their conjugates, matching alpha_lambda wedge bar(alpha_mu). *)
Definition ordered_mixed_one_form (j : 'I_(n+n)) := mixed_basis_one_form he (split j).

(** Source for [ordered_mixed_one_form_basisP]: Federer 1.6.6,
    p. 27, mixed basis in degree one, in the order used for increasing
    products in every degree. *)
Theorem ordered_mixed_one_form_basisP : is_basis ordered_mixed_one_form.
Proof.
exact: (@basis_reindex C (Choice.clone J _) (Choice.clone 'I_(n+n) _)
  (complex_valued_form embed VR C^o 1) (mixed_basis_one_form he)
  (mixed_one_form_basisP he) (@unsplit n n) (@split n n) (@unsplitK n n) (@splitK n n)).
Qed.
End Ordered.
