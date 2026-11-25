(** Federer (1969), 4.1.12, p. 369:
    the original phi_i vanishes at
    every u_j and at every v_j
    except v_i, where it equals one.
    Use its actual support in the
    consecutive open interval, not assumed interpolation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate AlternatingForms AlternatingZero
  CurrentSpaces CurrentSupportGeometry CurrentFormSupportValues SmoothTestSpaces WeightedIntervalEndpoints
  WeightedIntervalCutoffUP WeightedIntervalCutoffSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section WeightedIntervalCutoffValues.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation phi := (@WeightedIntervalCutoff.value R h2).
Local Notation value := (@current_test_value R h2 1%N Full hFull 0%N).
Local Notation support := (@current_test_support R h2 1%N 0%N Full hFull).
Local Notation hE := (@current_smooth_space_laws R h2 1%N Full hFull 0%N).

(** Source for [weighted_interval_cutoff_left_value]:
    each original phi_i vanishes at
    every original left endpoint u_j,
    supporting T(phi_i)=i in Federer
    4.1.12, p. 369. *)
Lemma weighted_interval_cutoff_left_value i j:
  value (phi i) (euclidean_one_embed (weighted_interval_left_endpoint R j))=0.
Proof.
have hNo:~support (phi i) (euclidean_one_embed (weighted_interval_left_endpoint R j)).
  move=>hSupport.
  have hBounds:weighted_interval_left_endpoint R i<
      euclidean_one_project (euclidean_one_embed (weighted_interval_left_endpoint R j))<
      weighted_interval_left_endpoint R i.+1:=
    (@WeightedIntervalCutoff.laws R h2 i).1 _ hSupport.
  rewrite euclidean_one_embedK in hBounds.
  have[hLow hHigh]:=andP hBounds.
  case:(leqP j i)=>hOrder.
  - have h:=@weighted_interval_left_endpoint_monotone R j i hOrder;exfalso;lra.
  - have h:=@weighted_interval_left_endpoint_monotone R i.+1 j hOrder;exfalso;lra.
exact:(@current_form_value_outside_support R h2 1%N 0%N Full hFull
  (smooth_test_inclusion hE (phi i)) _ Logic.I hNo).
Qed.

(** Source for [weighted_interval_cutoff_right_value]:
    each original phi_i takes value
    one precisely at its own v_i
    among the original right endpoints,
    supporting Federer 4.1.12, p. 369. *)
Lemma weighted_interval_cutoff_right_value i j:
  value (phi i) (euclidean_one_embed (weighted_interval_right_endpoint R j))=
    @zero_form R X R^o (if j==i then 1 else 0).
Proof.
case:(eqVneq j i)=>hEqual.
- subst j;exact:(@WeightedIntervalCutoff.laws R h2 i).2.2.1.
- have hNo:~support (phi i) (euclidean_one_embed (weighted_interval_right_endpoint R j)).
    move=>hSupport.
    have hBounds:weighted_interval_left_endpoint R i<
        euclidean_one_project (euclidean_one_embed (weighted_interval_right_endpoint R j))<
        weighted_interval_left_endpoint R i.+1:=
      (@WeightedIntervalCutoff.laws R h2 i).1 _ hSupport.
    rewrite euclidean_one_embedK in hBounds.
    have[hLow hHigh]:=andP hBounds.
    have[_ [hJLow hJHigh]]:=@weighted_interval_endpoint_order R j.
    case:(ltngtP j i)=>[hJI|hIJ|hSame];last by subst j;rewrite eqxx in hEqual.
    * have h:=@weighted_interval_left_endpoint_monotone R j.+1 i hJI;exfalso;lra.
    * have h:=@weighted_interval_left_endpoint_monotone R i.+1 j hIJ;exfalso;lra.
  have hZero:value (phi i) (euclidean_one_embed (weighted_interval_right_endpoint R j))=0.
    exact:(@current_form_value_outside_support R h2 1%N 0%N Full hFull
      (smooth_test_inclusion hE (phi i)) _ Logic.I hNo).
  rewrite hZero.
  exact:esym (linear0 (@zero_form R X R^o)).
Qed.
End WeightedIntervalCutoffValues.
