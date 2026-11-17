(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 332:
    every original fibre contains at most
    k points. The original first equation
    gives monic roots; the other equations
    and the supplied basis distinguish those points. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals.
From Federer Require Import Hom LinearBasis GrassmannAbbreviations FiniteCoordinates
  FieldPrefixCoordinatesUP OrdinalCoordinateTail FieldPolynomialFibreSeparation
  FieldMonicLowerCoefficientExtension FieldFiniteFibreFromRootInjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteFibres.
Variable R:fieldType.
Variable X:lmodType R.
Variables n m:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Hypothesis hMN:(m<=n)%N.
Local Notation Y:=(coordinate_space R m).
Local Notation tail:=(ordinal_coordinate_tail_index hMN).
Variable P:Hom X Y.
Hypothesis hP:is_field_prefix_projection omega hMN P.
Variable first:'I_(n-m).
Variable k:nat.
Variable delta:Y->R.
Variable b0:'I_k->Y->R.
Variable b:'I_(n-m)->'I_k->Y->R.
Variable Z:set X.
Hypothesis hNonzero:forall x,Z x ->delta (P x)!=0.
Hypothesis hRoot:forall x,Z x ->
  (omega (tail first) x)^+k+\sum_(i<k) b0 i (P x)*(omega (tail first) x)^+(i:nat) = 0.
Hypothesis hRelations:forall x,Z x ->forall j,j!=first ->
  delta (P x)*omega (tail j) x = \sum_(i<k) b j i (P x)*(omega (tail first) x)^+(i:nat).

(** Source for [field_polynomial_finite_fibres]:
    the fibres have cardinality nu in
    {0,...,k}, 3.4.8(10), p. 332.
    The original equations supply every root
    and the restricted injection. No finite-fibre
    or fibre-count premise is introduced. *)
Theorem field_polynomial_finite_fibres (y:Y):
  finite_set [set x|Z x /\P x = y] /\
    forall s:seq X,uniq s ->(forall x,x \in s ->Z x /\P x = y) ->(size s<=k)%N.
Proof.
pose F:set X:=fun x=>Z x /\P x = y.
pose xi:=fun x:X=>omega (tail first) x.
have [c [hLeading [hLower hValue]]]:=@field_monic_lower_coefficient_extension R k (fun i=>b0 i y).
have hRoots x (hx:F x): \sum_(i<k.+1) c i*(xi x)^+(i:nat) = 0.
  rewrite hValue /xi.
  have h:=@hRoot x hx.1;by rewrite hx.2 in h.
have hInjective x z (hx:F x) (hz:F z):xi x=xi z ->x=z.
  move=>hFirst.
  have hDelta:delta y!=0 by rewrite -hx.2;exact:hNonzero x hx.1.
  have hPrefix:P x = P z by rewrite hx.2 hz.2.
  pose t:=fun j:'I_(n-m)=>\sum_(i<k) b j i y*(xi x)^+(i:nat).
  have hX j (hj:j!=first):delta y*omega (tail j) x = t j.
    have h:=@hRelations x hx.1 j hj;by rewrite hx.2 in h.
  have hZ j (hj:j!=first):delta y*omega (tail j) z = t j.
    have h:=@hRelations z hz.1 j hj.
    rewrite hz.2 in h;change (delta y*omega (tail j) z =
      \sum_(i<k) b j i y*(xi z)^+(i:nat)) in h.
    by rewrite -hFirst in h.
  exact:(@field_polynomial_fibre_separation R X n m e he omega hDual hMN P hP first
    x z (delta y) t hDelta hPrefix hFirst hX hZ).
exact:(@field_finite_fibre_from_monic_root_injection R [the choiceType of (X:Type)] F k c xi
  hLeading hRoots hInjective).
Qed.
End FiniteFibres.
