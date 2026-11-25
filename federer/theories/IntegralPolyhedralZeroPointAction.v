(** Federer (1969), 4.1.24, p. 381: every
    integral polyhedral zero-current has the original
    finite integer point-action laws. Apply the least
    generated-subgroup law, reusing the actual Dirac
    zero-simplex and the already proved subgroup of
    real integers. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp functions
  classical_sets reals.
From Federer Require Import Hom Bilinear TopologicalGroupUP RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingZero SmoothCompactSet CurrentSpaces CurrentPointEvaluation CurrentDirac
  VitaliNonmeasurableSet GeneratedAdditiveSubgroupUP PolyhedralCurrentGenerators
  PolyhedralCurrentAlgebra FiniteIntegerPointActionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.
Local Open Scope ring_scope.

Section IntegralPolyhedralZeroPointAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X:=(R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU 0%N).
Local Notation DT:=(@current_test_space R h2 n U hU 0%N).
Local Notation action:=(@current_value R h2 n U hU 0%N).
Local Notation Good:=(@has_finite_integer_point_action R h2 n U hU K).

(** Source for [finite_integer_point_action_subgroup]: zero,
    addition and inversion preserve finite integer point
    actions, including repeated points, 4.1.24, p. 381. *)
Theorem finite_integer_point_action_subgroup:
  is_subgroup (fun T S:C=>T+S) (fun T=>-T) 0 Good.
Proof.
constructor.
- exists fset0;split;first by move=>x;rewrite in_fset0.
  constructor.
  + move=>phi psi _.
    by rewrite (lin0 (hom_linear action)) !hom_zeroE.
  + move=>phi _.
    change (@real_integers R (@current_point_evaluation R h2 n 0%N U hU phi 0)).
    rewrite (lin0 (hom_linear (@current_point_evaluation R h2 n 0%N U hU phi))).
    exact:subgroup_unit (@real_integers_subgroup R).
- move=>T S [H [hHK hH]] [J [hJK hJ]].
  have hHL:forall x,x\in H->x\in(H `|` J).
    by move=>x hx;rewrite in_fsetU hx.
  have hJR:forall x,x\in J->x\in(H `|` J).
    by move=>x hx;rewrite in_fsetU hx orbT.
  exists (H `|` J);split.
  + move=>x;rewrite in_fsetU=>/orP[hx|hx];[exact:hHK x hx|exact:hJK x hx].
  + constructor.
    * move=>phi psi hEqual.
      pose E:=@current_point_evaluation R h2 n 0%N U hU phi.
      pose F:=@current_point_evaluation R h2 n 0%N U hU psi.
      change (E (T+S)=F (T+S)).
      rewrite (linD (hom_linear E)) (linD (hom_linear F)).
      have hT:=finite_integer_point_action_locality (phi:=phi) (psi:=psi) hH
        (fun x hx=>hEqual x (@hHL x hx)).
      have hS:=finite_integer_point_action_locality (phi:=phi) (psi:=psi) hJ
        (fun x hx=>hEqual x (@hJR x hx)).
      change (E T=F T) in hT;change (E S=F S) in hS;by rewrite hT hS.
    * move=>phi hInteger.
      pose E:=@current_point_evaluation R h2 n 0%N U hU phi.
      change (@real_integers R (E (T+S))).
      rewrite (linD (hom_linear E)).
      apply:(subgroup_mul (@real_integers_subgroup R)).
      -- exact:(finite_integer_point_action_integrality (phi:=phi) hH
          (fun x hx=>hInteger x (@hHL x hx))).
      -- exact:(finite_integer_point_action_integrality (phi:=phi) hJ
          (fun x hx=>hInteger x (@hJR x hx))).
- move=>T [H [hHK hH]];exists H;split;first exact:hHK.
  constructor.
  + move=>phi psi hEqual.
    pose E:=@current_point_evaluation R h2 n 0%N U hU phi.
    pose F:=@current_point_evaluation R h2 n 0%N U hU psi.
    change (E (-T)=F (-T));rewrite -[-T]sub0r (linB (hom_linear E)) (linB (hom_linear F))
      (lin0 (hom_linear E)) (lin0 (hom_linear F)) !sub0r.
    have h:=finite_integer_point_action_locality (phi:=phi) (psi:=psi) hH hEqual.
    change (E T=F T) in h;by rewrite h.
  + move=>phi hInteger.
    pose E:=@current_point_evaluation R h2 n 0%N U hU phi.
    change (@real_integers R (E (-T)));
    rewrite -[-T]sub0r (linB (hom_linear E)) (lin0 (hom_linear E)) sub0r.
    apply:(subgroup_inv (@real_integers_subgroup R)).
    exact:(finite_integer_point_action_integrality (phi:=phi) hH hInteger).
Qed.

(** Source for [integral_polyhedral_zero_finite_integer_point_action]:
    every original integral polyhedral zero-current has
    finite integer point data in the same K,
    as used for R_0=P-script_0 in 4.1.24, p. 381. *)
Theorem integral_polyhedral_zero_finite_integer_point_action (T:C):
  @integral_polyhedral_current_class R h2 n 0%N U hU K T->Good T.
Proof.
apply:(generated_additive_subgroup_least
  (@integral_polyhedral_current_class_laws R h2 n 0%N U hU K)
  finite_integer_point_action_subgroup).
move=>P [v [hHull <-]].
rewrite open_oriented_simplex_point.
pose x:=v ord0.
have hx:smooth_compact_carrier K x.
  exact:(@polyhedral_simplex_vertices_in_index R n 0%N U K v hHull ord0).1.
exists [fset x];split.
- move=>y /fset1P ->;exact:hx.
- constructor.
  + move=>phi psi hEqual;rewrite !dirac_current_evaluation.
    exact:hEqual x (fset11 x).
  + move=>phi hInteger;rewrite dirac_current_evaluation.
    exact:hInteger x (fset11 x).
Qed.
End IntegralPolyhedralZeroPointAction.
