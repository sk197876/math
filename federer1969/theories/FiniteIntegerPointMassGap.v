(** Federer (1969), 4.1.24, p. 381: a nonzero
    integral polyhedral zero-current has mass at least
    one. The original finite point-action laws and
    unit-comass tests isolate each integer multiplicity.
    This proof retains empty finite point sets and
    all cancellation. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp functions
  classical_sets reals constructive_ereal.
From Federer Require Import Hom Bilinear TopologicalGroupUP RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingZero CurrentSpaces CurrentEvaluation CurrentTestPointValues
  CurrentZeroCovectorMaps CurrentGlobalComassSealed CurrentGlobalComassBound
  CurrentMassSealed CurrentMassFiniteAlgebra SmoothCompactSet
  VitaliNonmeasurableSet FiniteIntegerPointActionUP CurrentFinitePointTestBasis
  IntegralPolyhedralZeroPointAction PolyhedralCurrentAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Open Scope ring_scope.

Section FiniteIntegerPointMassGap.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU 0%N).
Local Notation DT:=(@current_test_space R h2 n U hU 0%N).
Local Notation ev:=(@current_test_value R h2 n U hU 0%N).
Local Notation action:=(@current_value R h2 n U hU 0%N).
Local Notation M:=(@CurrentMass.value R h2 n 0%N U hU).
Local Notation coeff phi x:=(zero_form_value (ev phi x)).

(** Source for [finite_integer_point_mass_gap]: original
    integral point multiplicities cannot have mass
    strictly between zero and one, the discrete
    zero-degree assertion of 4.1.24, p. 381. *)
Theorem finite_integer_point_mass_gap (T:C):
  @has_finite_integer_point_action R h2 n U hU K T->
  (M T<1)%E->T=0.
Proof.
move=>[H [hHK hH]] hMass.
have hHU:forall x,x\in H->U x.
  move=>x hx;exact:smooth_compact_in_domain K x (hHK x hx).
have[gamma [hCoordinates hComass]]:=@current_finite_point_test_basis_exists
  R h2 n U hU H hHU.
have hInt0:@real_integers R 0:=subgroup_unit (@real_integers_subgroup R).
have hInt1:@real_integers R 1 by exists 1%Z;rewrite mulr1z.
have hGammaZero (i:H):action T (gamma i)=0.
  have hInteger:@real_integers R (action T (gamma i)).
    apply:(finite_integer_point_action_integrality hH).
    move=>x hx;pose j:H:=[` hx]%fset.
    change (@real_integers R (coeff (gamma i) (val j))).
    rewrite (hCoordinates i j);case:ifP=>_;[exact:hInt1|exact:hInt0].
  have hUnit:(@CurrentGlobalComass.value R h2 n 0%N U (ev (gamma i))<=1)%E.
    exact:(@current_global_comass_bound R h2 n 0%N U (ev (gamma i)) 1).2 (hComass i).
  have hSmall:=le_lt_trans
    (@current_mass_unit_absolute R h2 n 0%N U hU T (gamma i) hUnit) hMass.
  rewrite lte_fin in hSmall.
  exact:real_integers_small hInteger hSmall.
apply:(@current_values_extensional R h2 n 0%N U hU)=>phi.
pose beta:DT:=\sum_(i:H) (coeff phi (val i))*:gamma i.
have hBasis:forall x,x\in H->coeff beta x=coeff phi x.
  move=>x hx;pose j:H:=[` hx]%fset.
  pose E:=hom_comp (@current_zero_form_coefficient R n)
    (@current_test_point_value_map R h2 n 0%N U hU (val j)).
  change (E beta=coeff phi (val j)).
  have hDiagonal:E ((coeff phi (val j))*:gamma j)=coeff phi (val j).
    rewrite linearZ;change ((coeff phi (val j))*coeff (gamma j) (val j)=coeff phi (val j)).
    by rewrite hCoordinates eqxx mulr1.
  rewrite /beta linear_sum (bigD1 j) //= big1 ?addr0.
    exact:hDiagonal.
  move=>i hIJ;change (E ((coeff phi (val i))*:gamma i)=0).
  rewrite linearZ;change ((coeff phi (val i))*coeff (gamma i) (val j)=0).
  by rewrite hCoordinates (negPf hIJ) mulr0.
have hAction:action T beta=0.
  rewrite /beta linear_sum;apply:big1=>i _.
  rewrite linearZ;change ((coeff phi (val i))*action T (gamma i)=0).
  by rewrite hGammaZero mulr0.
have hEqual:=finite_integer_point_action_locality (phi:=phi) (psi:=beta) hH
  (fun x hx=>esym (hBasis x hx)).
rewrite hEqual hAction (lin0 (hom_linear action)) hom_zeroE.
by [].
Qed.

(** Source for [integral_polyhedral_zero_mass_gap]: a
    nonzero member of the original integral polyhedral
    zero-current class has mass at least one,
    as used in R_0=P-script_0, 4.1.24, p. 381. *)
Theorem integral_polyhedral_zero_mass_gap (T:C):
  @integral_polyhedral_current_class R h2 n 0%N U hU K T->
  (M T<1)%E->T=0.
Proof.
move=>hT;exact:finite_integer_point_mass_gap
  (@integral_polyhedral_zero_finite_integer_point_action R h2 n U hU K T hT).
Qed.
End FiniteIntegerPointMassGap.
